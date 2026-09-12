/-
`Language.JavaScript.JSNumber.parse?` reads a numeric literal *in place*: it
scans the spelling by byte index, skipping the numeric separators where they
are written, so that reading a literal allocates nothing.  It used to build
the list of the characters of the spelling, filter the separators out of it,
and walk the result with `List.span`.

This module proves that the two read the same literal.  The reader which was
replaced is transcribed as `JSNumber.parseChars?`, and the main result is

* `JSNumber.parse?_eq_parseChars?` : `parse? raw = parseChars? raw`.

It is proved in two steps, through `parseList?` — the same one pass reader
as `parse?`, written on a `List Char`:

* `parse?_eq_parseList?` says that scanning by byte index is walking the
  list of characters (this is where the byte positions are reasoned about,
  with the `ByteScan` toolkit of `LanguageJavascript.RegExpLitSpec`);
* `parseList?_eq_parseCharsList?` says that the one pass reader computes
  what the `filter`/`span` based one computed.
-/
-- import Mathlib.Data.List.TakeDrop
import LanguageJavascript.RegExpLitSpec

set_option autoImplicit false

namespace Language.JavaScript

open ByteScan

namespace ByteScan

/-- The number of bytes a list of characters occupies does not depend on
their order. -/
theorem blen_reverse (l : List Char) : blen l.reverse = blen l := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [blen_append, ih, Nat.add_comm]

theorem utf8PrevAux_append (c : Char) (suf : List Char) : ∀ (pre : List Char) (i : Nat),
    String.Pos.Raw.utf8PrevAux (pre ++ c :: suf) ⟨i⟩ ⟨i + blen pre + c.utf8Size⟩
      = ⟨i + blen pre⟩ := by
  intro pre
  induction pre with
  | nil =>
    intro i
    have hle : (⟨i + 0 + c.utf8Size⟩ : String.Pos.Raw) ≤ (⟨i⟩ : String.Pos.Raw) + c := by
      simp [String.Pos.Raw.le_iff]
    simp only [List.nil_append, String.Pos.Raw.utf8PrevAux, blen_nil, ite_eq_left hle]
    simp
  | cons d ds ih =>
    intro i
    have hdpos := d.utf8Size_pos
    have hcpos := c.utf8Size_pos
    have hnle : ¬ ((⟨i + blen (d :: ds) + c.utf8Size⟩ : String.Pos.Raw)
        ≤ (⟨i⟩ : String.Pos.Raw) + d) := by
      simp only [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_add_char, blen_cons]
      omega
    simp only [List.cons_append, String.Pos.Raw.utf8PrevAux, ite_eq_right hnle]
    have hadd : (⟨i⟩ : String.Pos.Raw) + d = ⟨i + d.utf8Size⟩ := rfl
    rw [hadd, show i + blen (d :: ds) + c.utf8Size
        = (i + d.utf8Size) + blen ds + c.utf8Size by simp only [blen_cons]; omega,
      ih (i + d.utf8Size)]
    simp only [blen_cons, String.Pos.Raw.mk.injEq]
    omega

/-- Stepping back from the position which follows `pre ++ [c]`. -/
theorem prev_eq {s : String} {pre suf : List Char} {c : Char}
    (h : s.toList = pre ++ c :: suf) :
    String.Pos.Raw.prev s ⟨blen pre + c.utf8Size⟩ = ⟨blen pre⟩ := by
  have : String.Pos.Raw.prev s ⟨blen pre + c.utf8Size⟩
      = String.Pos.Raw.utf8PrevAux (pre ++ c :: suf) ⟨0⟩ ⟨0 + blen pre + c.utf8Size⟩ := by
    rw [show 0 + blen pre + c.utf8Size = blen pre + c.utf8Size by omega, ← h]
    rfl
  rw [this, utf8PrevAux_append]
  simp

end ByteScan

namespace JSNumber

/-! ## The one pass reader, on a list of characters

Each function below is the list version of the scanner of the same name:
what the scanner does between two byte indices, it does on the characters
between them. -/

/-- The next character which is not a numeric separator, the characters
consumed to reach it (the separators and the character itself), and what
follows it. -/
def nextCharList? : List Char → Option (Char × List Char × List Char)
  | [] => none
  | c :: cs =>
      if c == '_' then (nextCharList? cs).map (fun r => (r.1, c :: r.2.1, r.2.2))
      else some (c, [c], cs)

/-- The value of the digits of `l` in base `radix`, `acc` being the value of
the digits read so far. -/
def digitsList? (radix : Nat) : List Char → Option Nat → Option Nat
  | [], acc => acc
  | c :: cs, acc =>
      if c == '_' then digitsList? radix cs acc
      else
        match digitVal? c with
        | none => none
        | some d =>
            if d < radix then digitsList? radix cs (some (radix * acc.getD 0 + d)) else none

/-- The mantissa of a base ten literal: its value, how many of its digits
are after the decimal point, the characters consumed (up to and including
the `e` which starts the exponent) and the characters which follow. -/
def mantissaList? : List Char → Nat → Nat → Nat → Bool →
    Option (Nat × Nat × List Char × List Char)
  | [], m, nd, nf, _ => if nd == 0 then none else some (m, nf, [], [])
  | c :: cs, m, nd, nf, dot =>
      if c == '_' then
        (mantissaList? cs m nd nf dot).map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
      else if c == '.' then
        if dot then none
        else (mantissaList? cs m nd nf true).map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
      else if c == 'e' || c == 'E' then
        if nd == 0 then none else some (m, nf, [c], cs)
      else
        match digitVal? c with
        | some d =>
            if d < 10 then
              (mantissaList? cs (10 * m + d) (nd + 1) (if dot then nf + 1 else nf) dot).map
                (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
            else none
        | none => none

/-- The exponent written by `l`: a sign and at least one digit, or nothing
at all, which is an exponent of zero. -/
def expList? (l : List Char) : Option Int :=
  match nextCharList? l with
  | none => some 0
  | some (c, _, cs) =>
      if c == '-' then (digitsList? 10 cs none).map (fun n => -(Int.ofNat n))
      else if c == '+' then (digitsList? 10 cs none).map Int.ofNat
      else (digitsList? 10 l none).map Int.ofNat

/-- The `n` suffix of a `BigInt` literal, looked for at the end of the
reversed spelling. -/
def bigSuffixAux : List Char → Option (List Char)
  | [] => none
  | c :: rs => if c == '_' then bigSuffixAux rs else if c == 'n' then some rs else none

/-- The characters which spell the digits of the literal, and whether it is
a `BigInt` one. -/
def bigSuffixList (l : List Char) : List Char × Bool :=
  match bigSuffixAux l.reverse with
  | some rs => (rs.reverse, true)
  | none => (l, false)

/-- A base ten literal, written by `mid`. -/
def parseDecimalList? (mid : List Char) (isBig : Bool) : Option JSNumber :=
  match mantissaList? mid 0 0 0 false with
  | none => none
  | some (m, nf, _, rest) =>
      match expList? rest with
      | none => none
      | some e =>
          if isBig then
            if nf == 0 && 0 ≤ e then some (.bigint .decimal (m * powNat 10 e.toNat)) else none
          else some (JSNumber.decimal m (e - Int.ofNat nf)).normalize

/-- The one pass reader, on a list of characters: exactly what `parse?`
does, with the byte indices replaced by the characters they point at. -/
def parseList? (l : List Char) : Option JSNumber :=
  let (mid, isBig) := bigSuffixList l
  match nextCharList? mid with
  | none => none
  | some (c0, _, rest0) =>
      if c0 == '0' then
        match nextCharList? rest0 with
        | none => parseDecimalList? mid isBig
        | some (c1, _, rest1) =>
            let base? : Option NumBase :=
              if c1 == 'x' || c1 == 'X' then some .hexadecimal
              else if c1 == 'o' || c1 == 'O' then some .octal
              else if c1 == 'b' || c1 == 'B' then some .binary
              else none
            match base? with
            | some b => (digitsList? b.radix rest1 none).map (ofRadixDigits isBig b)
            | none =>
                match digitsList? 8 rest0 none with
                | some v => some (ofRadixDigits isBig .octal v)
                | none => parseDecimalList? mid isBig
      else parseDecimalList? mid isBig

/-! ## The reader which was replaced -/

/-- The value of a list of digits in base `radix`; `none` if the list is
empty, or holds a character which is not a digit of that base. -/
def digitsVal? (radix : Nat) : List Char → Option Nat
  | [] => none
  | cs => cs.foldl (fun acc c => do
      let a ← acc
      let d ← digitVal? c
      if d < radix then some (radix * a + d) else none) (some 0)

/-- The reader a numeric literal used to be read with: the spelling becomes
a list of characters, the numeric separators are filtered out of it, and the
result is split with `List.span`. -/
def parseCharsList? (l : List Char) : Option JSNumber := do
  let cs := (l.filter (· ≠ '_'))
  if cs.isEmpty then none else
  let (cs, isBig) :=
    match cs.reverse with
    | 'n' :: rest => (rest.reverse, true)
    | _ => (cs, false)
  if cs.isEmpty then none else
  let prefixed : Option (NumBase × List Char) :=
    match cs with
    | '0' :: c :: rest =>
        if c == 'x' || c == 'X' then some (.hexadecimal, rest)
        else if c == 'o' || c == 'O' then some (.octal, rest)
        else if c == 'b' || c == 'B' then some (.binary, rest)
        else if '0' ≤ c && c ≤ '7' && rest.all (fun d => '0' ≤ d && d ≤ '7') then
          some (.octal, c :: rest)
        else none
    | _ => none
  match prefixed with
  | some (b, ds) =>
      let v ← digitsVal? b.radix ds
      some (if isBig then .bigint b v else (JSNumber.radix b v).normalize)
  | none =>
      -- a base ten literal: `intPart [. fracPart] [e [+-] expPart]`
      let (mantissaChars, expChars) :=
        match cs.span (fun c => c ≠ 'e' && c ≠ 'E') with
        | (m, []) => (m, ([] : List Char))
        | (m, _ :: e) => (m, e)
      let (intChars, fracChars) :=
        match mantissaChars.span (· ≠ '.') with
        | (i, []) => (i, ([] : List Char))
        | (i, _ :: f) => (i, f)
      if intChars.isEmpty && fracChars.isEmpty then none else
      let digits := intChars ++ fracChars
      let mantissa ← if digits.isEmpty then some 0 else digitsVal? 10 digits
      let expValue : Option Int :=
        match expChars with
        | [] => some 0
        | '-' :: ds => (digitsVal? 10 ds).map (fun n => -(Int.ofNat n))
        | '+' :: ds => (digitsVal? 10 ds).map Int.ofNat
        | ds => (digitsVal? 10 ds).map Int.ofNat
      let e ← expValue
      if isBig then
        if fracChars.isEmpty && e ≥ 0 then
          some (.bigint .decimal (mantissa * powNat 10 e.toNat))
        else none
      else
        some (JSNumber.decimal mantissa (e - Int.ofNat fracChars.length)).normalize

/-- The reader a numeric literal used to be read with. -/
def parseChars? (raw : String) : Option JSNumber := parseCharsList? raw.toList

/-! ## Scanning by byte index is walking the list of characters -/

/-- What `nextCharList?` consumes is a prefix of its input. -/
theorem nextCharList?_split : ∀ (l : List Char) (c : Char) (cons rest : List Char),
    nextCharList? l = some (c, cons, rest) → l = cons ++ rest := by
  intro l
  induction l with
  | nil => intro c cons rest h; simp [nextCharList?] at h
  | cons d ds ih =>
    intro c cons rest h
    simp only [nextCharList?] at h
    by_cases hd : d == '_'
    · rw [ite_eq_left hd] at h
      cases hrec : nextCharList? ds with
      | none => rw [hrec] at h; simp at h
      | some r =>
        rw [hrec] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hcons, hrest⟩ := h
        subst hcons; subst hrest
        have := ih r.1 r.2.1 r.2.2 (by rw [hrec])
        simpa using this
    · rw [ite_eq_right hd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hc, hcons, hrest⟩ := h
      subst hc; subst hcons; subst hrest
      rfl

theorem nextChar?_eq (raw : String) : ∀ (suf pre post : List Char) (fuel : Nat),
    raw.toList = pre ++ suf ++ post → suf.length ≤ fuel →
    nextChar? raw (blen pre + blen suf) fuel ⟨blen pre⟩
      = (nextCharList? suf).map (fun r => (r.1, (⟨blen pre + blen r.2.1⟩ : String.Pos.Raw))) := by
  intro suf
  induction suf with
  | nil =>
    intro pre post fuel _ _
    cases fuel <;> simp [nextChar?, nextCharList?]
  | cons c cs ih =>
    intro pre post fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hstop : ¬ (blen pre + blen (c :: cs) ≤ blen pre) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hs' : raw.toList = pre ++ c :: (cs ++ post) := by rw [hs]; simp
      have hget : String.Pos.Raw.get raw ⟨blen pre⟩ = c := get_eq hs'
      have hnext : String.Pos.Raw.next raw ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs'
      simp only [nextChar?, ite_eq_right hstop, hget, hnext, nextCharList?]
      by_cases hu : c == '_'
      · rw [ite_eq_left hu, ite_eq_left hu]
        have hrec := ih (pre ++ [c]) post n (by rw [hs]; simp) (by simp at hfuel; omega)
        have hstop' : blen (pre ++ [c]) + blen cs = blen pre + blen (c :: cs) := by
          simp only [blen_append, blen_cons, blen_nil]; omega
        rw [hstop'] at hrec
        rw [hrec]
        cases nextCharList? cs with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
            String.Pos.Raw.mk.injEq, blen_append, blen_cons, blen_nil]
          exact ⟨trivial, by omega⟩
      · rw [ite_eq_right hu, ite_eq_right hu]
        simp only [Option.map_some,
          blen_append, blen_cons, blen_nil]

theorem digitsFrom?_eq (raw : String) : ∀ (suf pre post : List Char) (radix : Nat)
    (acc : Option Nat) (fuel : Nat),
    raw.toList = pre ++ suf ++ post → suf.length ≤ fuel →
    digitsFrom? raw (blen pre + blen suf) radix fuel ⟨blen pre⟩ acc
      = digitsList? radix suf acc := by
  intro suf
  induction suf with
  | nil =>
    intro pre post radix acc fuel _ _
    cases fuel <;> simp [digitsFrom?, digitsList?]
  | cons c cs ih =>
    intro pre post radix acc fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hstop : ¬ (blen pre + blen (c :: cs) ≤ blen pre) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hs' : raw.toList = pre ++ c :: (cs ++ post) := by rw [hs]; simp
      have hget : String.Pos.Raw.get raw ⟨blen pre⟩ = c := get_eq hs'
      have hnext : String.Pos.Raw.next raw ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs'
      have hstop' : blen (pre ++ [c]) + blen cs = blen pre + blen (c :: cs) := by
        simp only [blen_append, blen_cons, blen_nil]; omega
      have hrec : ∀ (a : Option Nat),
          digitsFrom? raw (blen pre + blen (c :: cs)) radix n ⟨blen (pre ++ [c])⟩ a
            = digitsList? radix cs a := by
        intro a
        have := ih (pre ++ [c]) post radix a n (by rw [hs]; simp) (by simp at hfuel; omega)
        rwa [hstop'] at this
      simp only [digitsFrom?, ite_eq_right hstop, hget, hnext, digitsList?]
      by_cases hu : c == '_'
      · rw [ite_eq_left hu, ite_eq_left hu]; exact hrec acc
      · rw [ite_eq_right hu, ite_eq_right hu]
        cases hdv : digitVal? c with
        | none => rfl
        | some d =>
          by_cases hlt : d < radix
          · simp only [ite_eq_left hlt]; exact hrec _
          · simp only [ite_eq_right hlt]

/-- What `mantissaList?` consumes is a prefix of its input. -/
theorem mantissaList?_split : ∀ (l : List Char) (m nd nf : Nat) (dot : Bool)
    (m' nf' : Nat) (cons rest : List Char),
    mantissaList? l m nd nf dot = some (m', nf', cons, rest) → l = cons ++ rest := by
  intro l
  induction l with
  | nil =>
    intro m nd nf dot m' nf' cons rest h
    simp only [mantissaList?] at h
    by_cases hnd : nd == 0
    · rw [ite_eq_left hnd] at h; simp at h
    · rw [ite_eq_right hnd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, hcons, hrest⟩ := h
      subst hcons; subst hrest; rfl
  | cons c cs ih =>
    intro m nd nf dot m' nf' cons rest h
    -- every branch but the `e` either prepends `c` to what is consumed, or fails
    have step : ∀ (a b e : Nat) (dt : Bool),
        (mantissaList? cs a b e dt).map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
          = some (m', nf', cons, rest) → c :: cs = cons ++ rest := by
      intro a b e dt hmap
      cases hrec : mantissaList? cs a b e dt with
      | none => rw [hrec] at hmap; simp at hmap
      | some r =>
        rw [hrec] at hmap
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨-, -, hcons, hrest⟩ := hmap
        subst hcons; subst hrest
        have := ih a b e dt r.1 r.2.1 r.2.2.1 r.2.2.2 (by rw [hrec])
        simpa using this
    simp only [mantissaList?] at h
    by_cases hu : c == '_'
    · rw [ite_eq_left hu] at h; exact step m nd nf dot h
    · rw [ite_eq_right hu] at h
      by_cases hdot : c == '.'
      · rw [ite_eq_left hdot] at h
        by_cases hd : dot
        · rw [ite_eq_left hd] at h; simp at h
        · rw [ite_eq_right hd] at h; exact step m nd nf true h
      · rw [ite_eq_right hdot] at h
        by_cases he : c == 'e' || c == 'E'
        · rw [ite_eq_left he] at h
          by_cases hnd : nd == 0
          · rw [ite_eq_left hnd] at h; simp at h
          · rw [ite_eq_right hnd] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, hcons, hrest⟩ := h
            subst hcons; subst hrest; rfl
        · rw [ite_eq_right he] at h
          cases hdv : digitVal? c with
          | none => simp [hdv] at h
          | some d =>
            simp only [hdv] at h
            by_cases hlt : d < 10
            · rw [ite_eq_left hlt] at h
              exact step (10 * m + d) (nd + 1) (if dot then nf + 1 else nf) dot h
            · rw [ite_eq_right hlt] at h; simp at h

theorem mantissaFrom?_eq (raw : String) : ∀ (suf pre post : List Char)
    (m nd nf : Nat) (dot : Bool) (fuel : Nat),
    raw.toList = pre ++ suf ++ post → suf.length ≤ fuel →
    mantissaFrom? raw (blen pre + blen suf) fuel ⟨blen pre⟩ m nd nf dot
      = (mantissaList? suf m nd nf dot).map
          (fun r => (r.1, r.2.1, (⟨blen pre + blen r.2.2.1⟩ : String.Pos.Raw))) := by
  intro suf
  induction suf with
  | nil =>
    intro pre post m nd nf dot fuel _ _
    cases fuel <;> (cases hnd : nd == 0 <;> simp [mantissaFrom?, mantissaList?, hnd])
  | cons c cs ih =>
    intro pre post m nd nf dot fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hstop : ¬ (blen pre + blen (c :: cs) ≤ blen pre) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hs' : raw.toList = pre ++ c :: (cs ++ post) := by rw [hs]; simp
      have hget : String.Pos.Raw.get raw ⟨blen pre⟩ = c := get_eq hs'
      have hnext : String.Pos.Raw.next raw ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs'
      have hstop' : blen (pre ++ [c]) + blen cs = blen pre + blen (c :: cs) := by
        simp only [blen_append, blen_cons, blen_nil]; omega
      have hrec : ∀ (a b e : Nat) (dt : Bool),
          mantissaFrom? raw (blen pre + blen (c :: cs)) n ⟨blen (pre ++ [c])⟩ a b e dt
            = ((mantissaList? cs a b e dt).map
                (fun r => (r.1, r.2.1, (⟨blen pre + blen (c :: r.2.2.1)⟩ : String.Pos.Raw)))) := by
        intro a b e dt
        have := ih (pre ++ [c]) post a b e dt n (by rw [hs]; simp) (by simp at hfuel; omega)
        rw [hstop'] at this
        rw [this]
        cases mantissaList? cs a b e dt with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
            String.Pos.Raw.mk.injEq, blen_append, blen_cons, blen_nil]
          exact ⟨trivial, trivial, by omega⟩
      simp only [mantissaFrom?, ite_eq_right hstop, hget, hnext, mantissaList?]
      by_cases hu : c == '_'
      · rw [ite_eq_left hu, ite_eq_left hu, hrec]
        cases mantissaList? cs m nd nf dot <;> rfl
      · rw [ite_eq_right hu, ite_eq_right hu]
        by_cases hdot : c == '.'
        · rw [ite_eq_left hdot, ite_eq_left hdot]
          by_cases hd : dot
          · rw [ite_eq_left hd, ite_eq_left hd]; rfl
          · rw [ite_eq_right hd, ite_eq_right hd, hrec]
            cases mantissaList? cs m nd nf true <;> rfl
        · rw [ite_eq_right hdot, ite_eq_right hdot]
          by_cases he : c == 'e' || c == 'E'
          · rw [ite_eq_left he, ite_eq_left he]
            by_cases hnd : nd == 0
            · rw [ite_eq_left hnd, ite_eq_left hnd]; rfl
            · rw [ite_eq_right hnd, ite_eq_right hnd]
              simp only [Option.map_some,
                blen_append, blen_cons, blen_nil]
          · rw [ite_eq_right he, ite_eq_right he]
            cases hdv : digitVal? c with
            | none => rfl
            | some d =>
              by_cases hlt : d < 10
              · simp only [ite_eq_left hlt]
                rw [hrec]
                cases mantissaList? cs (10 * m + d) (nd + 1)
                  (if dot then nf + 1 else nf) dot <;> rfl
              · simp only [ite_eq_right hlt]; rfl

theorem expFrom?_eq (raw : String) (suf pre post : List Char) (fuel : Nat)
    (h : raw.toList = pre ++ suf ++ post) (hfuel : suf.length ≤ fuel) :
    expFrom? raw (blen pre + blen suf) fuel ⟨blen pre⟩ = expList? suf := by
  have hnext := nextChar?_eq raw suf pre post fuel h hfuel
  simp only [expFrom?, expList?, hnext]
  cases hnc : nextCharList? suf with
  | none => rfl
  | some r =>
    obtain ⟨c, cons, rest⟩ := r
    have hsplit : suf = cons ++ rest := nextCharList?_split suf c cons rest hnc
    have hlen : rest.length ≤ fuel := by
      have : suf.length = cons.length + rest.length := by rw [hsplit]; simp
      omega
    have hpre : raw.toList = (pre ++ cons) ++ rest ++ post := by
      rw [h, hsplit]; simp
    have hstop : blen (pre ++ cons) + blen rest = blen pre + blen suf := by
      rw [hsplit]; simp only [blen_append]; omega
    have hdig : ∀ (radix : Nat) (acc : Option Nat),
        digitsFrom? raw (blen pre + blen suf) radix fuel ((⟨blen pre + blen cons⟩ :
            String.Pos.Raw)) acc = digitsList? radix rest acc := by
      intro radix acc
      have := digitsFrom?_eq raw rest (pre ++ cons) post radix acc fuel hpre hlen
      rw [hstop] at this
      simpa only [blen_append] using this
    have hdig0 : ∀ (radix : Nat) (acc : Option Nat),
        digitsFrom? raw (blen pre + blen suf) radix fuel ((⟨blen pre⟩ : String.Pos.Raw)) acc
          = digitsList? radix suf acc := by
      intro radix acc
      exact digitsFrom?_eq raw suf pre post radix acc fuel h hfuel
    simp only [Option.map_some]
    by_cases hm : c == '-'
    · rw [ite_eq_left hm, ite_eq_left hm, hdig]
    · rw [ite_eq_right hm, ite_eq_right hm]
      by_cases hp : c == '+'
      · rw [ite_eq_left hp, ite_eq_left hp, hdig]
      · rw [ite_eq_right hp, ite_eq_right hp, hdig0]

/-- The backward scan for the `n` suffix, on the reversed spelling: `rmid`
is what is left to scan, reversed, and `post` what has been scanned past
(only separators). -/
theorem bigSuffix_eq_aux (raw : String) : ∀ (rmid post : List Char) (fuel : Nat),
    raw.toList = rmid.reverse ++ post → rmid.length ≤ fuel →
    bigSuffix raw raw.utf8ByteSize fuel ⟨blen rmid⟩
      = (match bigSuffixAux rmid with
         | some rs => (blen rs, true)
         | none => (raw.utf8ByteSize, false)) := by
  intro rmid
  induction rmid with
  | nil =>
    intro post fuel _ _
    cases fuel <;> simp [bigSuffix, bigSuffixAux]
  | cons c rs ih =>
    intro post fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hs' : raw.toList = rs.reverse ++ c :: post := by
      rw [hs]; simp
    have hblen : blen (c :: rs) = blen rs.reverse + c.utf8Size := by
      rw [blen_reverse]; simp only [blen_cons]; omega
    have hzero : ¬ ((⟨blen (c :: rs)⟩ : String.Pos.Raw).byteIdx = 0) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hprev : String.Pos.Raw.prev raw ⟨blen (c :: rs)⟩ = ⟨blen rs.reverse⟩ := by
        rw [hblen]; exact prev_eq hs'
      have hget : String.Pos.Raw.get raw ⟨blen rs.reverse⟩ = c := get_eq hs'
      have hrev : blen rs.reverse = blen rs := blen_reverse rs
      simp only [bigSuffix, hzero, hprev, hget, bigSuffixAux,
        ite_false, beq_iff_eq]
      by_cases hu : c = '_'
      · rw [ite_eq_left hu, ite_eq_left hu]
        have := ih (c :: post) n (by rw [hs]; simp) (by simp at hfuel; omega)
        rw [← hrev] at this
        exact this
      · rw [ite_eq_right hu, ite_eq_right hu]
        by_cases hn : c = 'n'
        · rw [ite_eq_left hn, ite_eq_left hn, hrev]
        · rw [ite_eq_right hn, ite_eq_right hn]

theorem bigSuffix_eq (raw : String) :
    bigSuffix raw raw.utf8ByteSize raw.utf8ByteSize ⟨raw.utf8ByteSize⟩
      = (blen (bigSuffixList raw.toList).1, (bigSuffixList raw.toList).2) := by
  have hlen : raw.toList.reverse.length ≤ raw.utf8ByteSize := by
    have := length_le_blen raw.toList
    simp only [blen_toList] at this
    simpa using this
  have hb : blen raw.toList.reverse = raw.utf8ByteSize := by
    rw [blen_reverse, blen_toList]
  have h := bigSuffix_eq_aux raw raw.toList.reverse [] raw.utf8ByteSize (by simp) hlen
  rw [hb] at h
  rw [h, bigSuffixList]
  cases bigSuffixAux raw.toList.reverse with
  | none => simp [blen_toList]
  | some rs => simp [blen_reverse]

/-- What the `n` suffix leaves is a prefix of the spelling. -/
theorem bigSuffixAux_split : ∀ (r rs : List Char), bigSuffixAux r = some rs → ∃ t, r = t ++ rs := by
  intro r
  induction r with
  | nil => intro rs h; simp [bigSuffixAux] at h
  | cons c cs ih =>
    intro rs h
    simp only [bigSuffixAux] at h
    by_cases hu : c == '_'
    · rw [ite_eq_left hu] at h
      obtain ⟨t, ht⟩ := ih rs h
      exact ⟨c :: t, by rw [ht]; simp⟩
    · rw [ite_eq_right hu] at h
      by_cases hn : c == 'n'
      · rw [ite_eq_left hn] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨[c], rfl⟩
      · rw [ite_eq_right hn] at h; simp at h

theorem bigSuffixList_split (l : List Char) : ∃ post, l = (bigSuffixList l).1 ++ post := by
  cases h : bigSuffixAux l.reverse with
  | none => exact ⟨[], by simp [bigSuffixList, h]⟩
  | some rs =>
    obtain ⟨t, ht⟩ := bigSuffixAux_split l.reverse rs h
    refine ⟨t.reverse, ?_⟩
    have hl : l = (t ++ rs).reverse := by rw [← ht]; simp
    simp only [bigSuffixList, h]
    rw [hl]; simp

/-- A prefix of the spelling has no more characters than the spelling has
bytes. -/
theorem length_le_utf8ByteSize {raw : String} {mid post : List Char}
    (h : raw.toList = mid ++ post) : mid.length ≤ raw.utf8ByteSize := by
  have hb : raw.toList.length ≤ raw.utf8ByteSize := by
    have := length_le_blen raw.toList
    simpa using this
  have : raw.toList.length = mid.length + post.length := by rw [h]; simp
  omega

theorem parseDecimal?_eq (raw : String) (mid post : List Char) (isBig : Bool)
    (h : raw.toList = mid ++ post) :
    parseDecimal? raw (blen mid) raw.utf8ByteSize isBig = parseDecimalList? mid isBig := by
  have hfuel : mid.length ≤ raw.utf8ByteSize := length_le_utf8ByteSize h
  have hm := mantissaFrom?_eq raw mid [] post 0 0 0 false raw.utf8ByteSize
    (by simpa using h) hfuel
  simp only [blen_nil, Nat.zero_add] at hm
  simp only [parseDecimal?, parseDecimalList?, hm]
  cases hml : mantissaList? mid 0 0 0 false with
  | none => rfl
  | some r =>
    obtain ⟨m, nf, cons, rest⟩ := r
    have hsplit : mid = cons ++ rest := mantissaList?_split mid 0 0 0 false m nf cons rest hml
    have hexp : expFrom? raw (blen mid) raw.utf8ByteSize ⟨blen cons⟩ = expList? rest := by
      have hpre : raw.toList = cons ++ rest ++ post := by simp [h, hsplit]
      have hlen : rest.length ≤ raw.utf8ByteSize := by
        have : mid.length = cons.length + rest.length := by rw [hsplit]; simp
        omega
      have hstop : blen cons + blen rest = blen mid := by
        rw [hsplit]; simp only [blen_append]
      have := expFrom?_eq raw rest cons post raw.utf8ByteSize hpre hlen
      rwa [hstop] at this
    simp only [Option.map_some, hexp]
    rfl

/-- The in-place reader reads the list of characters of its input. -/
theorem parse?_eq_parseList? (raw : String) : parse? raw = parseList? raw.toList := by
  obtain ⟨post, hpost⟩ := bigSuffixList_split raw.toList
  have hfuel : (bigSuffixList raw.toList).1.length ≤ raw.utf8ByteSize :=
    length_le_utf8ByteSize hpost
  have hbs := bigSuffix_eq raw
  -- the digits of the literal, and whether it is a `BigInt` one
  rcases hbl : bigSuffixList raw.toList with ⟨mid, isBig⟩
  rw [hbl] at hpost hbs hfuel
  simp only at hpost hbs hfuel
  have hnext0 : nextChar? raw (blen mid) raw.utf8ByteSize ⟨0⟩
      = (nextCharList? mid).map (fun r => (r.1, (⟨blen r.2.1⟩ : String.Pos.Raw))) := by
    have := nextChar?_eq raw mid [] post raw.utf8ByteSize (by simpa using hpost) hfuel
    simpa using this
  have hdec := parseDecimal?_eq raw mid post isBig hpost
  simp only [parse?, hbs, parseList?, hbl, hnext0, hdec]
  cases hnc : nextCharList? mid with
  | none => rfl
  | some r0 =>
    obtain ⟨c0, cons0, rest0⟩ := r0
    have hsplit0 : mid = cons0 ++ rest0 := nextCharList?_split mid c0 cons0 rest0 hnc
    have hpre0 : raw.toList = cons0 ++ rest0 ++ post := by simp [hpost, hsplit0]
    have hlen0 : rest0.length ≤ raw.utf8ByteSize := by
      have : mid.length = cons0.length + rest0.length := by rw [hsplit0]; simp
      omega
    have hstop0 : blen cons0 + blen rest0 = blen mid := by
      rw [hsplit0]; simp only [blen_append]
    have hnext1 : nextChar? raw (blen mid) raw.utf8ByteSize ⟨blen cons0⟩
        = (nextCharList? rest0).map
            (fun r => (r.1, (⟨blen cons0 + blen r.2.1⟩ : String.Pos.Raw))) := by
      have := nextChar?_eq raw rest0 cons0 post raw.utf8ByteSize hpre0 hlen0
      rwa [hstop0] at this
    have hdig0 : ∀ (radix : Nat) (acc : Option Nat),
        digitsFrom? raw (blen mid) radix raw.utf8ByteSize ⟨blen cons0⟩ acc
          = digitsList? radix rest0 acc := by
      intro radix acc
      have := digitsFrom?_eq raw rest0 cons0 post radix acc raw.utf8ByteSize hpre0 hlen0
      rwa [hstop0] at this
    simp only [Option.map_some, hnext1]
    by_cases hzero : c0 == '0'
    · rw [ite_eq_left hzero, ite_eq_left hzero]
      cases hnc1 : nextCharList? rest0 with
      | none => simp only [Option.map_none]
      | some r1 =>
        obtain ⟨c1, cons1, rest1⟩ := r1
        have hsplit1 : rest0 = cons1 ++ rest1 := nextCharList?_split rest0 c1 cons1 rest1 hnc1
        have hpre1 : raw.toList = (cons0 ++ cons1) ++ rest1 ++ post := by
          simp [hpost, hsplit0, hsplit1]
        have hlen1 : rest1.length ≤ raw.utf8ByteSize := by
          have : rest0.length = cons1.length + rest1.length := by rw [hsplit1]; simp
          omega
        have hstop1 : blen (cons0 ++ cons1) + blen rest1 = blen mid := by
          rw [hsplit0, hsplit1]; simp only [blen_append]; omega
        have hdig1 : ∀ (radix : Nat) (acc : Option Nat),
            digitsFrom? raw (blen mid) radix raw.utf8ByteSize ⟨blen cons0 + blen cons1⟩ acc
              = digitsList? radix rest1 acc := by
          intro radix acc
          have := digitsFrom?_eq raw rest1 (cons0 ++ cons1) post radix acc raw.utf8ByteSize
            hpre1 hlen1
          rw [hstop1] at this
          simpa only [blen_append] using this
        simp only [Option.map_some, hdig1, hdig0]
        rfl
    · rw [ite_eq_right hzero, ite_eq_right hzero]

/-! ## The one pass reader computes what the `span` based one computed -/

/-- The characters of `l` which are not numeric separators — what the reader
which was replaced started by building. -/
def filterSep (l : List Char) : List Char := l.filter (fun c => c != '_')

@[simp] theorem filterSep_nil : filterSep [] = [] := rfl

theorem filterSep_cons (c : Char) (cs : List Char) :
    filterSep (c :: cs) = if c == '_' then filterSep cs else c :: filterSep cs := by
  by_cases h : c = '_'
  · subst h; simp [filterSep]
  · simp [filterSep, h]

theorem filterSep_eq_filter (l : List Char) : filterSep l = l.filter (· ≠ '_') := by
  simp only [filterSep]
  congr 1
  funext c
  by_cases h : c = '_' <;> simp [h]

theorem filterSep_append (l m : List Char) :
    filterSep (l ++ m) = filterSep l ++ filterSep m := by
  simp [filterSep, List.filter_append]

theorem filterSep_reverse (l : List Char) : filterSep l.reverse = (filterSep l).reverse := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.reverse_cons, filterSep_append, ih, filterSep_cons]
    by_cases h : c = '_'
    · subst h; simp [filterSep]
    · simp [filterSep, h]

/-- Reading digits from left to right, starting from `acc`. -/
def foldStep (radix : Nat) : Option Nat → List Char → Option Nat
  | acc, [] => acc
  | acc, c :: cs =>
      match acc with
      | none => none
      | some a =>
          match digitVal? c with
          | none => none
          | some d => if d < radix then foldStep radix (some (radix * a + d)) cs else none

@[simp] theorem foldStep_none (radix : Nat) (cs : List Char) :
    foldStep radix none cs = none := by
  cases cs <;> rfl

/-- The value of a list of digits is the fold, once there is a digit. -/
theorem digitsVal?_eq_foldStep (radix : Nat) (cs : List Char) :
    digitsVal? radix cs = if cs.isEmpty then none else foldStep radix (some 0) cs := by
  have hfold : ∀ (l : List Char) (a : Option Nat),
      l.foldl (fun acc c => do
        let x ← acc
        let d ← digitVal? c
        if d < radix then some (radix * x + d) else none) a = foldStep radix a l := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons c cs ih =>
      intro a
      cases a with
      | none => simpa using ih none
      | some x =>
        cases hdv : digitVal? c with
        | none => simpa [foldStep, hdv] using ih none
        | some d =>
          by_cases hlt : d < radix
          · simpa [foldStep, hdv, hlt] using ih (some (radix * x + d))
          · simpa [foldStep, hdv, hlt] using ih none
  cases cs with
  | nil => rfl
  | cons c cs => simpa [digitsVal?] using hfold (c :: cs) (some 0)

/-- Reading digits in place skips the separators, which is reading the
digits of the filtered list. -/
theorem digitsList?_some (radix : Nat) : ∀ (l : List Char) (a : Nat),
    digitsList? radix l (some a) = foldStep radix (some a) (filterSep l) := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons c cs ih =>
    intro a
    simp only [digitsList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]; exact ih a
    · rw [ite_eq_right hu, ite_eq_right hu]
      cases hdv : digitVal? c with
      | none => simp [foldStep, hdv]
      | some d =>
        by_cases hlt : d < radix
        · simp only [ite_eq_left hlt, foldStep, hdv, Option.getD_some]
          exact ih _
        · simp [foldStep, hdv, hlt]

theorem digitsList?_none (radix : Nat) (l : List Char) :
    digitsList? radix l none = digitsVal? radix (filterSep l) := by
  rw [digitsVal?_eq_foldStep]
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [digitsList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]; exact ih
    · rw [ite_eq_right hu, ite_eq_right hu]
      cases hdv : digitVal? c with
      | none => simp [foldStep, hdv]
      | some d =>
        by_cases hlt : d < radix
        · simp only [ite_eq_left hlt, Option.getD_none, List.isEmpty_cons, Bool.false_eq_true,
            ite_false, foldStep, hdv]
          rw [digitsList?_some]
        · simp [foldStep, hdv, hlt]

/-- The next character which is not a separator is the head of the filtered
list. -/
theorem nextCharList?_filter : ∀ (l : List Char),
    (nextCharList? l).map (fun r => (r.1, filterSep r.2.2))
      = (match filterSep l with
         | [] => none
         | c :: cs => some (c, cs)) := by
  intro l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [nextCharList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]
      rw [← ih]
      cases nextCharList? cs <;> rfl
    · rw [ite_eq_right hu, ite_eq_right hu]
      rfl

/-! ### The reader which was replaced, restructured

The `match`es of `parseCharsList?` are written as functions below, which is
the same computation — `parseCharsList?_eq_alt` — in a shape the proofs can
work with. -/

/-- Split at the first `e`; the `e` itself is dropped. -/
def splitE : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if c == 'e' || c == 'E' then ([], cs)
      else (c :: (splitE cs).1, (splitE cs).2)

/-- Split at the first decimal point; the point itself is dropped. -/
def splitDot : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if c == '.' then ([], cs)
      else (c :: (splitDot cs).1, (splitDot cs).2)

/-- The `n` suffix of a `BigInt` literal, at the head of the reversed
spelling. -/
def stripBigList (l : List Char) : Option (List Char) :=
  match l with
  | [] => none
  | c :: rs => if c == 'n' then some rs else none

/-- The exponent of a base ten literal, as the reader which was replaced
read it. -/
def oldExp (cs : List Char) : Option Int :=
  match cs with
  | [] => some 0
  | '-' :: ds => (digitsVal? 10 ds).map (fun n => -(Int.ofNat n))
  | '+' :: ds => (digitsVal? 10 ds).map Int.ofNat
  | ds => (digitsVal? 10 ds).map Int.ofNat

/-- A base ten literal, as the reader which was replaced read it: the tail
of `parseCharsList?`, verbatim. -/
def oldDecimal (cs : List Char) (isBig : Bool) : Option JSNumber := do
  let (mantissaChars, expChars) :=
    match cs.span (fun c => c ≠ 'e' && c ≠ 'E') with
    | (m, []) => (m, ([] : List Char))
    | (m, _ :: e) => (m, e)
  let (intChars, fracChars) :=
    match mantissaChars.span (· ≠ '.') with
    | (i, []) => (i, ([] : List Char))
    | (i, _ :: f) => (i, f)
  if intChars.isEmpty && fracChars.isEmpty then none else
  let digits := intChars ++ fracChars
  let mantissa ← if digits.isEmpty then some 0 else digitsVal? 10 digits
  let e ← oldExp expChars
  if isBig then
    if fracChars.isEmpty && e ≥ 0 then
      some (.bigint .decimal (mantissa * powNat 10 e.toNat))
    else none
  else
    some (JSNumber.decimal mantissa (e - Int.ofNat fracChars.length)).normalize

/-- The same, with the two `span`s written as `splitE` and `splitDot`. -/
def oldDecimalSplit (cs : List Char) (isBig : Bool) : Option JSNumber := do
  let (mantissaChars, expChars) := splitE cs
  let (intChars, fracChars) := splitDot mantissaChars
  if intChars.isEmpty && fracChars.isEmpty then none else
  let digits := intChars ++ fracChars
  let mantissa ← if digits.isEmpty then some 0 else digitsVal? 10 digits
  let e ← oldExp expChars
  if isBig then
    if fracChars.isEmpty && e ≥ 0 then
      some (.bigint .decimal (mantissa * powNat 10 e.toNat))
    else none
  else
    some (JSNumber.decimal mantissa (e - Int.ofNat fracChars.length)).normalize

/-- The digits of the literal, as the reader which was replaced read
them. -/
def oldCore (cs : List Char) (isBig : Bool) : Option JSNumber :=
  match cs with
  | '0' :: c :: rest =>
      if c == 'x' || c == 'X' then
        (digitsVal? 16 rest).map (ofRadixDigits isBig .hexadecimal)
      else if c == 'o' || c == 'O' then
        (digitsVal? 8 rest).map (ofRadixDigits isBig .octal)
      else if c == 'b' || c == 'B' then
        (digitsVal? 2 rest).map (ofRadixDigits isBig .binary)
      else if '0' ≤ c && c ≤ '7' && rest.all (fun d => '0' ≤ d && d ≤ '7') then
        (digitsVal? 8 (c :: rest)).map (ofRadixDigits isBig .octal)
      else oldDecimalSplit ('0' :: c :: rest) isBig
  | cs => oldDecimalSplit cs isBig

/-- The reader which was replaced, restructured. -/
def parseCharsAlt? (l : List Char) : Option JSNumber :=
  let cs0 := filterSep l
  let (cs, isBig) :=
    match stripBigList cs0.reverse with
    | some rest => (rest.reverse, true)
    | none => (cs0, false)
  if cs.isEmpty then none else oldCore cs isBig

theorem List.span_loop_eq {α : Type} (p : α → Bool) (as : List α) (acc : List α) :
    List.span.loop p as acc = (acc.reverse ++ as.takeWhile p, as.dropWhile p) := by
  induction as generalizing acc with
  | nil => simp [List.span.loop]
  | cons a as ih =>
    simp [List.span.loop]
    split <;> rename_i h
    · rw [ih (a :: acc)]
      simp [List.takeWhile, List.dropWhile, h]
    · simp [List.takeWhile, List.dropWhile, h]

theorem List.span_eq_takeWhile_dropWhile {α : Type} (p : α → Bool) (l : List α) :
    l.span p = (l.takeWhile p, l.dropWhile p) := by
  simp [List.span, span_loop_eq]

theorem splitE_eq (cs : List Char) :
    (match cs.span (fun c => c ≠ 'e' && c ≠ 'E') with
     | (m, []) => (m, ([] : List Char))
     | (m, _ :: e) => (m, e)) = splitE cs := by
  simp only [List.span_eq_takeWhile_dropWhile]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = 'e'
    · subst h1; simp [splitE]
    · by_cases h2 : c = 'E'
      · subst h2; simp [splitE]
      · have hp : (decide (c ≠ 'e') && decide (c ≠ 'E')) = true := by simp [h1, h2]
        rw [List.takeWhile_cons, List.dropWhile_cons, ite_eq_left hp, ite_eq_left hp]
        have hsplit : splitE (c :: cs) = (c :: (splitE cs).1, (splitE cs).2) := by
          simp [splitE, h1, h2]
        rw [hsplit, ← ih]
        cases List.dropWhile (fun c => decide (c ≠ 'e') && decide (c ≠ 'E')) cs <;> rfl

theorem splitDot_eq (cs : List Char) :
    (match cs.span (· ≠ '.') with
     | (i, []) => (i, ([] : List Char))
     | (i, _ :: f) => (i, f)) = splitDot cs := by
  simp only [List.span_eq_takeWhile_dropWhile]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '.'
    · subst h1; simp [splitDot]
    · have hp : decide (c ≠ '.') = true := by simp [h1]
      rw [List.takeWhile_cons, List.dropWhile_cons, ite_eq_left hp, ite_eq_left hp]
      have hsplit : splitDot (c :: cs) = (c :: (splitDot cs).1, (splitDot cs).2) := by
        simp [splitDot, h1]
      rw [hsplit, ← ih]
      cases List.dropWhile (fun c => decide (c ≠ '.')) cs <;> rfl

/-- The body of `parseCharsList?`, verbatim: what it computes once the
separators are gone and the `n` suffix has been read. -/
def parseCharsBody (cs : List Char) (isBig : Bool) : Option JSNumber := do
  let prefixed : Option (NumBase × List Char) :=
    match cs with
    | '0' :: c :: rest =>
        if c == 'x' || c == 'X' then some (.hexadecimal, rest)
        else if c == 'o' || c == 'O' then some (.octal, rest)
        else if c == 'b' || c == 'B' then some (.binary, rest)
        else if '0' ≤ c && c ≤ '7' && rest.all (fun d => '0' ≤ d && d ≤ '7') then
          some (.octal, c :: rest)
        else none
    | _ => none
  match prefixed with
  | some (b, ds) =>
      let v ← digitsVal? b.radix ds
      some (if isBig then .bigint b v else (JSNumber.radix b v).normalize)
  | none => oldDecimal cs isBig

theorem parseCharsList?_eq_body (l : List Char) :
    parseCharsList? l =
      (if (l.filter (· ≠ '_')).isEmpty then none
       else
         let (cs, isBig) :=
           match (l.filter (· ≠ '_')).reverse with
           | 'n' :: rest => (rest.reverse, true)
           | _ => (l.filter (· ≠ '_'), false)
         if cs.isEmpty then none else parseCharsBody cs isBig) := rfl

/-- Reading the `n` suffix off the reversed spelling. -/
theorem strip_match (cs : List Char) :
    (match cs.reverse with
     | 'n' :: rest => (rest.reverse, true)
     | _ => (cs, false))
      = (match stripBigList cs.reverse with
         | some rest => (rest.reverse, true)
         | none => (cs, false)) := by
  cases h : cs.reverse with
  | nil => rfl
  | cons d ds =>
    by_cases hd : d = 'n'
    · subst hd; simp [stripBigList]
    · simp [stripBigList, hd]

theorem oldDecimal_eq_split (cs : List Char) (isBig : Bool) :
    oldDecimal cs isBig = oldDecimalSplit cs isBig := by
  simp only [oldDecimal, oldDecimalSplit, splitE_eq, splitDot_eq]

theorem parseCharsBody_eq_oldCore (cs : List Char) (isBig : Bool) :
    parseCharsBody cs isBig = oldCore cs isBig := by
  match cs with
  | [] => simp only [parseCharsBody, oldCore, oldDecimal_eq_split]
  | [c0] => simp only [parseCharsBody, oldCore, oldDecimal_eq_split]
  | c0 :: c1 :: rest1 =>
    by_cases h0 : c0 = '0'
    · subst h0
      simp only [parseCharsBody, oldCore, oldDecimal_eq_split, NumBase.radix]
      by_cases hx : c1 == 'x' || c1 == 'X'
      · simp only [ite_eq_left hx]; cases digitsVal? 16 rest1 <;> rfl
      · simp only [ite_eq_right hx]
        by_cases ho : c1 == 'o' || c1 == 'O'
        · simp only [ite_eq_left ho]; cases digitsVal? 8 rest1 <;> rfl
        · simp only [ite_eq_right ho]
          by_cases hb : c1 == 'b' || c1 == 'B'
          · simp only [ite_eq_left hb]; cases digitsVal? 2 rest1 <;> rfl
          · simp only [ite_eq_right hb]
            by_cases hoct : '0' ≤ c1 && c1 ≤ '7' && rest1.all (fun d => '0' ≤ d && d ≤ '7')
            · simp only [ite_eq_left hoct]; cases digitsVal? 8 (c1 :: rest1) <;> rfl
            · simp only [ite_eq_right hoct]
    · simp only [parseCharsBody, oldCore, oldDecimal_eq_split, NumBase.radix]
      split <;> rename_i heq <;> simp_all

theorem parseCharsList?_eq_alt (l : List Char) : parseCharsList? l = parseCharsAlt? l := by
  rw [parseCharsList?_eq_body, ← filterSep_eq_filter]
  simp only [parseCharsAlt?, strip_match, parseCharsBody_eq_oldCore]
  cases hf : filterSep l with
  | nil => simp [stripBigList]
  | cons a as => simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]

theorem octal_of_digit {c : Char} {d : Nat} (h : digitVal? c = some d) (hlt : d < 8) :
    ('0' ≤ c && c ≤ '7') = true := by
  have hc : c.toNat = c.val.toNat := rfl
  have e0 : ('0' : Char).toNat = 48 := rfl
  have ea : ('a' : Char).toNat = 97 := rfl
  have eA : ('A' : Char).toNat = 65 := rfl
  have v0 : ('0' : Char).val.toNat = 48 := rfl
  have v7 : ('7' : Char).val.toNat = 55 := rfl
  have v9 : ('9' : Char).val.toNat = 57 := rfl
  have va : ('a' : Char).val.toNat = 97 := rfl
  have vf : ('f' : Char).val.toNat = 102 := rfl
  have vA : ('A' : Char).val.toNat = 65 := rfl
  have vF : ('F' : Char).val.toNat = 70 := rfl
  simp only [digitVal?] at h
  by_cases h9 : ('0' ≤ c && c ≤ '9') = true
  · rw [ite_eq_left h9] at h
    simp only [Option.some.injEq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h9 ⊢
    omega
  · rw [ite_eq_right h9] at h
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not, Char.le_def,
      UInt32.le_iff_toNat_le, Nat.not_le] at h9
    by_cases hf : ('a' ≤ c && c ≤ 'f') = true
    · rw [ite_eq_left hf] at h
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def,
        UInt32.le_iff_toNat_le] at hf
      omega
    · rw [ite_eq_right hf] at h
      by_cases hF : ('A' ≤ c && c ≤ 'F') = true
      · rw [ite_eq_left hF] at h
        simp only [Option.some.injEq] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def,
          UInt32.le_iff_toNat_le] at hF
        omega
      · rw [ite_eq_right hF] at h
        exact absurd h (by simp)

theorem digit_of_octal {c : Char} (h : ('0' ≤ c && c ≤ '7') = true) :
    ∃ d, digitVal? c = some d ∧ d < 8 := by
  have hc : c.toNat = c.val.toNat := rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
    show ('0' : Char).val.toNat = 48 from rfl, show ('7' : Char).val.toNat = 55 from rfl] at h
  have h9 : ('0' ≤ c && c ≤ '9') = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
      show ('0' : Char).val.toNat = 48 from rfl, show ('9' : Char).val.toNat = 57 from rfl]
    omega
  refine ⟨c.toNat - '0'.toNat, ?_, ?_⟩
  · simp [digitVal?, h9]
  · simp only [hc, show ('0' : Char).toNat = 48 from rfl]
    omega

theorem foldStep8_isSome : ∀ (cs : List Char) (a : Nat),
    (foldStep 8 (some a) cs).isSome = cs.all (fun d => '0' ≤ d && d ≤ '7') := by
  intro cs
  induction cs with
  | nil => intro a; rfl
  | cons c cs ih =>
    intro a
    simp only [foldStep, List.all_cons]
    cases hdv : digitVal? c with
    | none =>
      have hc : ('0' ≤ c && c ≤ '7') = false := by
        by_cases hcon : ('0' ≤ c && c ≤ '7') = true
        · have ⟨d, hd, _⟩ := digit_of_octal hcon
          rw [hdv] at hd; cases hd
        · cases h : ('0' ≤ c && c ≤ '7')
          · rfl
          · contradiction
      simp [hc]
    | some d =>
      by_cases hlt : d < 8
      · have hc : ('0' ≤ c && c ≤ '7') = true := octal_of_digit hdv hlt
        simp only [ite_eq_left hlt, hc, Bool.true_and]
        exact ih _
      · have hc : ('0' ≤ c && c ≤ '7') = false := by
          by_cases hcon : ('0' ≤ c && c ≤ '7') = true
          · have ⟨d', hd', hlt'⟩ := digit_of_octal hcon
            rw [hdv, Option.some.injEq] at hd'
            omega
          · cases h : ('0' ≤ c && c ≤ '7')
            · rfl
            · contradiction
        simp [hlt, hc]

theorem digitsVal?_octal_guard (c : Char) (rest : List Char) :
    (digitsVal? 8 (c :: rest)).isSome
      = ('0' ≤ c && c ≤ '7' && rest.all (fun d => '0' ≤ d && d ≤ '7')) := by
  rw [digitsVal?_eq_foldStep]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
  rw [foldStep8_isSome]
  simp [List.all_cons]

/-- Looking for the `n` suffix while skipping the separators is looking for
it in the filtered list. -/
theorem bigSuffixAux_filter : ∀ (r : List Char),
    (bigSuffixAux r).map filterSep = stripBigList (filterSep r) := by
  intro r
  induction r with
  | nil => rfl
  | cons c cs ih =>
    simp only [bigSuffixAux, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]; exact ih
    · rw [ite_eq_right hu, ite_eq_right hu]
      by_cases hn : c == 'n'
      · rw [ite_eq_left hn]; simp [stripBigList, hn]
      · rw [ite_eq_right hn]; simp [stripBigList, hn]

/-- Reading the `n` suffix in place, then filtering, is filtering, then
reading the `n` suffix. -/
theorem bigSuffixList_filter (l : List Char) :
    (filterSep (bigSuffixList l).1, (bigSuffixList l).2)
      = (match stripBigList (filterSep l).reverse with
         | some rest => (rest.reverse, true)
         | none => (filterSep l, false)) := by
  rw [show (filterSep l).reverse = filterSep l.reverse from (filterSep_reverse l).symm,
    ← bigSuffixAux_filter]
  simp only [bigSuffixList]
  cases h : bigSuffixAux l.reverse with
  | none => simp
  | some rs => simp [filterSep_reverse]

theorem oldExp_cons (c : Char) (ds : List Char) (hm : ¬ c = '-') (hp : ¬ c = '+') :
    oldExp (c :: ds) = (digitsVal? 10 (c :: ds)).map Int.ofNat := by
  unfold oldExp
  split <;> rename_i heq <;> simp_all

/-- Reading the exponent in place is reading it off the filtered list. -/
theorem expList?_eq (l : List Char) : expList? l = oldExp (filterSep l) := by
  have hf := nextCharList?_filter l
  cases h : nextCharList? l with
  | none =>
    rw [h] at hf
    simp only [Option.map_none] at hf
    cases hfl : filterSep l with
    | nil => simp [expList?, h, oldExp]
    | cons a as => rw [hfl] at hf; simp at hf
  | some r =>
    obtain ⟨c, cons, cs⟩ := r
    rw [h] at hf
    simp only [Option.map_some] at hf
    cases hfl : filterSep l with
    | nil => rw [hfl] at hf; simp at hf
    | cons a as =>
      rw [hfl] at hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, hcs⟩ := hf
      simp only [expList?, h, digitsList?_none, hcs, hfl]
      by_cases hm : c = '-'
      · subst hm; simp [oldExp]
      · by_cases hp : c = '+'
        · subst hp; simp [oldExp]
        · rw [ite_eq_right (by simpa using hm), ite_eq_right (by simpa using hp), oldExp_cons c as hm hp]

/-- The digits of the integer part of a mantissa, as the reader which was
replaced split them off: nothing at all once the decimal point has been
read. -/
def oldMantI (cs : List Char) (dot : Bool) : List Char :=
  if dot then [] else (splitDot (splitE cs).1).1

/-- The digits of the fractional part of a mantissa, as the reader which was
replaced split them off: everything, once the decimal point has been read. -/
def oldMantF (cs : List Char) (dot : Bool) : List Char :=
  if dot then (splitE cs).1 else (splitDot (splitE cs).1).2

/-- The characters the mantissa reader consumed do not matter to what the
value it read is: they are dropped. -/
theorem map_consumed (c : Char) (X : Option (Nat × Nat × List Char × List Char)) :
    (X.map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))).map
        (fun r => (r.1, r.2.1, filterSep r.2.2.2))
      = X.map (fun r => (r.1, r.2.1, filterSep r.2.2.2)) := by
  cases X <;> rfl

/-- Reading the mantissa in place, skipping the separators, is reading it
off the filtered list. -/
theorem mantissaList?_filter : ∀ (cs : List Char) (m nd nf : Nat) (dot : Bool),
    (mantissaList? cs m nd nf dot).map (fun r => (r.1, r.2.1, filterSep r.2.2.2))
      = (if nd == 0 && (oldMantI (filterSep cs) dot ++ oldMantF (filterSep cs) dot).isEmpty then
           none
         else
           (foldStep 10 (some m)
               (oldMantI (filterSep cs) dot ++ oldMantF (filterSep cs) dot)).map
             (fun m' => (m', nf + (oldMantF (filterSep cs) dot).length,
               (splitE (filterSep cs)).2))) := by
  intro cs
  induction cs with
  | nil =>
    intro m nd nf dot
    simp only [mantissaList?, filterSep_nil, oldMantI, oldMantF, splitE, splitDot]
    cases dot <;> by_cases hnd : nd == 0 <;> simp [hnd, foldStep]
  | cons c cs ih =>
    intro m nd nf dot
    simp only [mantissaList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu, map_consumed]
      exact ih m nd nf dot
    · rw [ite_eq_right hu, ite_eq_right hu]
      by_cases hdot : c == '.'
      · have hc : c = '.' := by simpa using hdot
        subst hc
        rw [ite_eq_left hdot]
        have hsE : splitE ('.' :: filterSep cs) = ('.' :: (splitE (filterSep cs)).1,
            (splitE (filterSep cs)).2) := by simp [splitE]
        cases dot with
        | true =>
          rw [ite_eq_left rfl]
          simp [oldMantI, oldMantF, hsE, foldStep, show digitVal? '.' = none from rfl]
        | false =>
          rw [ite_eq_right (by simp), map_consumed, ih m nd nf true]
          have h1 : oldMantI ('.' :: filterSep cs) false = oldMantI (filterSep cs) true := by
            simp [oldMantI, hsE, splitDot]
          have h2 : oldMantF ('.' :: filterSep cs) false = oldMantF (filterSep cs) true := by
            simp [oldMantF, hsE, splitDot]
          rw [h1, h2]
          simp only [hsE]
      · rw [ite_eq_right hdot]
        have hcd : ¬ c = '.' := by simpa using hdot
        by_cases he : c == 'e' || c == 'E'
        · rw [ite_eq_left he]
          have hsE : splitE (c :: filterSep cs) = ([], filterSep cs) := by simp [splitE, he]
          by_cases hnd : nd == 0
          · simp [hnd, oldMantI, oldMantF, hsE, splitDot]
          · simp [hnd, oldMantI, oldMantF, hsE, splitDot, foldStep]
        · rw [ite_eq_right he]
          have hsE : splitE (c :: filterSep cs) = (c :: (splitE (filterSep cs)).1,
              (splitE (filterSep cs)).2) := by simp [splitE, he]
          have hsD : splitDot (c :: (splitE (filterSep cs)).1)
              = (c :: (splitDot (splitE (filterSep cs)).1).1,
                 (splitDot (splitE (filterSep cs)).1).2) := by simp [splitDot, hcd]
          have hIt : oldMantI (c :: filterSep cs) true = [] := by simp [oldMantI]
          have hIt' : oldMantI (filterSep cs) true = [] := by simp [oldMantI]
          have hFt : oldMantF (c :: filterSep cs) true
              = c :: oldMantF (filterSep cs) true := by simp [oldMantF, hsE]
          have hIf : oldMantI (c :: filterSep cs) false
              = c :: oldMantI (filterSep cs) false := by simp [oldMantI, hsE, hsD]
          have hFf : oldMantF (c :: filterSep cs) false
              = oldMantF (filterSep cs) false := by simp [oldMantF, hsE, hsD]
          cases hdv : digitVal? c with
          | none =>
            dsimp only
            cases dot with
            | true =>
              rw [hIt, hFt]
              simp [foldStep, hdv, hsE]
            | false =>
              rw [hIf, hFf]
              simp [foldStep, hdv, hsE]
          | some d =>
            dsimp only
            by_cases hlt : d < 10
            · rw [ite_eq_left hlt, map_consumed,
                ih (10 * m + d) (nd + 1) (if dot then nf + 1 else nf) dot]
              cases dot with
              | true =>
                rw [hIt, hIt', hFt]
                simp only [hsE, List.nil_append, List.isEmpty_cons, Bool.and_false,
                  Bool.false_eq_true, ite_false, foldStep, hdv, ite_eq_left hlt, List.length_cons]
                match foldStep 10 (some (10 * m + d)) (oldMantF (filterSep cs) true) with
                | none => simp
                | some v => simp; omega
              | false =>
                rw [hIf, hFf]
                simp only [hsE, List.cons_append, List.isEmpty_cons, Bool.and_false,
                  Bool.false_eq_true, ite_false, foldStep, hdv, ite_eq_left hlt]
                simp
            · rw [ite_eq_right hlt]
              cases dot with
              | true =>
                rw [hIt, hFt]
                simp [foldStep, hdv, hlt, hsE]
              | false =>
                rw [hIf, hFf]
                simp [foldStep, hdv, hlt, hsE]

/-- A base ten literal, as the reader which was replaced read it, with the
two splits named. -/
def oldDecimalCore (cs : List Char) (isBig : Bool) : Option JSNumber :=
  if (oldMantI cs false ++ oldMantF cs false).isEmpty then none
  else
    match foldStep 10 (some 0) (oldMantI cs false ++ oldMantF cs false) with
    | none => none
    | some mantissa =>
        match oldExp (splitE cs).2 with
        | none => none
        | some e =>
            if isBig then
              (if (oldMantF cs false).isEmpty && e ≥ 0 then
                 some (.bigint .decimal (mantissa * powNat 10 e.toNat))
               else none)
            else some (JSNumber.decimal mantissa (e - Int.ofNat (oldMantF cs false).length)).normalize

/-- A concatenation is empty exactly when both of its parts are. -/
theorem isEmpty_append (l m : List Char) :
    (l ++ m).isEmpty = (l.isEmpty && m.isEmpty) := by
  cases l <;> simp

theorem oldDecimalSplit_eq_core (cs : List Char) (isBig : Bool) :
    oldDecimalSplit cs isBig = oldDecimalCore cs isBig := by
  simp only [oldDecimalSplit, oldDecimalCore, oldMantI, oldMantF, Bool.false_eq_true, ite_false,
    isEmpty_append]
  by_cases h1 : ((splitDot (splitE cs).1).1.isEmpty && (splitDot (splitE cs).1).2.isEmpty) = true
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    have h2 : ((splitDot (splitE cs).1).1 ++ (splitDot (splitE cs).1).2).isEmpty = false := by
      simp only [isEmpty_append, Bool.and_eq_true] at h1 ⊢
      simpa using h1
    rw [ite_eq_right h1, digitsVal?_eq_foldStep, ite_eq_right (by rw [h2]; simp)]
    cases foldStep 10 (some 0) ((splitDot (splitE cs).1).1 ++ (splitDot (splitE cs).1).2) with
    | none => rfl
    | some v => cases oldExp (splitE cs).2 <;> rfl

/-- Reading a base ten literal in place, skipping the separators, is reading
it off the filtered list. -/
theorem parseDecimalList?_filter (mid : List Char) (isBig : Bool) :
    parseDecimalList? mid isBig = oldDecimalCore (filterSep mid) isBig := by
  have hm := mantissaList?_filter mid 0 0 0 false
  simp only [beq_self_eq_true, Bool.true_and, Nat.zero_add] at hm
  cases hml : mantissaList? mid 0 0 0 false with
  | none =>
    rw [hml] at hm
    simp only [Option.map_none] at hm
    simp only [parseDecimalList?, hml, oldDecimalCore]
    by_cases hE : (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false).isEmpty = true
    · rw [ite_eq_left hE]
    · rw [ite_eq_right hE] at hm ⊢
      cases hfs : foldStep 10 (some 0)
          (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false) with
      | none => rfl
      | some v => rw [hfs] at hm; simp at hm
  | some r =>
    obtain ⟨m, nf, cons, rest⟩ := r
    rw [hml] at hm
    simp only [Option.map_some] at hm
    by_cases hE : (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false).isEmpty = true
    · rw [ite_eq_left hE] at hm; simp at hm
    · rw [ite_eq_right hE] at hm
      cases hfs : foldStep 10 (some 0)
          (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false) with
      | none => rw [hfs] at hm; simp at hm
      | some v =>
        rw [hfs] at hm
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨hm1, hm2, hm3⟩ := hm
        subst hm1
        subst hm2
        simp only [parseDecimalList?, hml, oldDecimalCore, ite_eq_right hE, hfs, expList?_eq, hm3]
        cases oldExp (splitE (filterSep mid)).2 with
        | none => rfl
        | some e =>
          have hlen : ((oldMantF (filterSep mid) false).length == 0)
              = (oldMantF (filterSep mid) false).isEmpty := by
            cases oldMantF (filterSep mid) false <;> simp
          cases isBig <;> simp [hlen, ge_iff_le]

/-- The body of `parseList?`, once the `n` suffix has been read. -/
def parseListCore (mid : List Char) (isBig : Bool) : Option JSNumber :=
  match nextCharList? mid with
  | none => none
  | some (c0, _, rest0) =>
      if c0 == '0' then
        match nextCharList? rest0 with
        | none => parseDecimalList? mid isBig
        | some (c1, _, rest1) =>
            let base? : Option NumBase :=
              if c1 == 'x' || c1 == 'X' then some .hexadecimal
              else if c1 == 'o' || c1 == 'O' then some .octal
              else if c1 == 'b' || c1 == 'B' then some .binary
              else none
            match base? with
            | some b => (digitsList? b.radix rest1 none).map (ofRadixDigits isBig b)
            | none =>
                match digitsList? 8 rest0 none with
                | some v => some (ofRadixDigits isBig .octal v)
                | none => parseDecimalList? mid isBig
      else parseDecimalList? mid isBig

theorem parseList?_eq_core (l : List Char) :
    parseList? l = parseListCore (bigSuffixList l).1 (bigSuffixList l).2 := rfl

/-- The one pass reader, on the digits of the literal, computes what the
reader which was replaced computed on the filtered ones. -/
theorem parseListCore_eq (mid : List Char) (isBig : Bool) :
    parseListCore mid isBig =
      (if (filterSep mid).isEmpty then none else oldCore (filterSep mid) isBig) := by
  have h0 := nextCharList?_filter mid
  cases hn : nextCharList? mid with
  | none =>
    rw [hn] at h0
    simp only [Option.map_none] at h0
    have hf : filterSep mid = [] := by
      cases hfl : filterSep mid with
      | nil => rfl
      | cons a as => rw [hfl] at h0; simp at h0
    simp only [parseListCore, hn, hf, List.isEmpty_nil, ite_true]
  | some r0 =>
    obtain ⟨c0, cons0, rest0⟩ := r0
    rw [hn] at h0
    simp only [Option.map_some] at h0
    have hf : filterSep mid = c0 :: filterSep rest0 := by
      cases hfl : filterSep mid with
      | nil => rw [hfl] at h0; simp at h0
      | cons a as =>
        rw [hfl] at h0
        simp only [Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨rfl, h⟩ := h0
        rw [h]
    rw [hf]
    simp only [parseListCore, hn, List.isEmpty_cons, Bool.false_eq_true, ite_false]
    by_cases hz : c0 == '0'
    · have hc0 : c0 = '0' := by simpa using hz
      subst hc0
      rw [ite_eq_left hz]
      have h1 := nextCharList?_filter rest0
      cases hn1 : nextCharList? rest0 with
      | none =>
        rw [hn1] at h1
        simp only [Option.map_none] at h1
        have hf1 : filterSep rest0 = [] := by
          cases hfl : filterSep rest0 with
          | nil => rfl
          | cons a as => rw [hfl] at h1; simp at h1
        rw [hf1, parseDecimalList?_filter, hf, hf1, oldCore, oldDecimalSplit_eq_core]
        intro c rest hcon
        simp at hcon
      | some r1 =>
        obtain ⟨c1, cons1, rest1⟩ := r1
        rw [hn1] at h1
        simp only [Option.map_some] at h1
        have hf1 : filterSep rest0 = c1 :: filterSep rest1 := by
          cases hfl : filterSep rest0 with
          | nil => rw [hfl] at h1; simp at h1
          | cons a as =>
            rw [hfl] at h1
            simp only [Option.some.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, h⟩ := h1
            rw [h]
        rw [hf1]
        simp only [oldCore, NumBase.radix, digitsList?_none, hf1]
        by_cases hx : c1 == 'x' || c1 == 'X'
        · simp only [ite_eq_left hx]
        · simp only [ite_eq_right hx]
          by_cases ho : c1 == 'o' || c1 == 'O'
          · simp only [ite_eq_left ho]
          · simp only [ite_eq_right ho]
            by_cases hb : c1 == 'b' || c1 == 'B'
            · simp only [ite_eq_left hb]
            · simp only [ite_eq_right hb]
              have hg := digitsVal?_octal_guard c1 (filterSep rest1)
              cases hdv : digitsVal? 8 (c1 :: filterSep rest1) with
              | some v =>
                rw [hdv] at hg
                simp only [Option.isSome_some] at hg
                rw [ite_eq_left hg.symm]
                rfl
              | none =>
                rw [hdv] at hg
                simp only [Option.isSome_none] at hg
                rw [ite_eq_right (by rw [← hg]; simp), parseDecimalList?_filter, hf, hf1,
                  oldDecimalSplit_eq_core]
    · rw [ite_eq_right hz, parseDecimalList?_filter, hf]
      have hoc : oldCore (c0 :: filterSep rest0) isBig
          = oldDecimalSplit (c0 :: filterSep rest0) isBig := by
        unfold oldCore
        split <;> rename_i heq <;> simp_all
      rw [hoc, oldDecimalSplit_eq_core]

theorem parseList?_eq_parseCharsList? (l : List Char) : parseList? l = parseCharsList? l := by
  rw [parseCharsList?_eq_alt, parseList?_eq_core, parseListCore_eq]
  have h := bigSuffixList_filter l
  simp only [parseCharsAlt?]
  rw [← h]

/-- The in-place reader reads exactly what the reader it replaced read. -/
theorem parse?_eq_parseChars? (raw : String) : parse? raw = parseChars? raw := by
  rw [parse?_eq_parseList?, parseChars?, parseList?_eq_parseCharsList?]

end JSNumber

end Language.JavaScript
