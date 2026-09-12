/-
The parser reads the text of a token — a name, a string literal, a chunk of
a template literal — *in place*: the characters are looked at, and the text
is sliced out, at the byte offsets the lexer recorded, so the text of the
token is never built as a string of its own and sliced afterwards.

This module proves that this reads exactly what the readers it replaced
read, which are the ones that take the text of the token as a `String`:

* `NEString.ofRange?_eq`         — a name;
* `JSStringSrc.ofRange?_eq`      — a string literal;
* `templateChunkRange_eq`        — a chunk of a template literal.

Each says: if the input `s` reads `pre ++ mid ++ rest`, then reading the
range which spells `mid` returns what the old reader returned on the string
`mid` spells.  The hypothesis is what says that the offsets are the ones of
a real token: they fall between characters, and multi-byte characters
before, inside and after the token are covered.

They rest on the toolkit of `RegExpLitSpec` (`ByteScan.blen`, `get_eq`,
`next_eq`, `extract_eq`), which this module extends with `ByteScan.prev_eq`,
the corresponding statement about `String.Pos.Raw.prev`.
-/
import LanguageJavascript.RegExpLitSpec
import LanguageJavascript.AST

set_option autoImplicit false

namespace Language.JavaScript

open ByteScan

namespace ByteScan

/-! ## Stepping back over a character -/

theorem utf8PrevAux_append (d : Char) (rest : List Char) : ∀ (pre : List Char) (i : Nat),
    String.Pos.Raw.utf8PrevAux (pre ++ d :: rest) ⟨i⟩ ⟨i + blen pre + d.utf8Size⟩
      = ⟨i + blen pre⟩ := by
  intro pre
  induction pre with
  | nil =>
    intro i
    simp only [List.nil_append, String.Pos.Raw.utf8PrevAux, blen_nil, Nat.add_zero]
    rw [ite_eq_left (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_add_char])]
  | cons c cs ih =>
    intro i
    have hc := c.utf8Size_pos
    have hd := d.utf8Size_pos
    have hadd : (⟨i⟩ : String.Pos.Raw) + c = ⟨i + c.utf8Size⟩ := rfl
    simp only [List.cons_append, String.Pos.Raw.utf8PrevAux, hadd]
    rw [show i + blen (c :: cs) + d.utf8Size = (i + c.utf8Size) + blen cs + d.utf8Size by
      simp only [blen_cons]; omega, ih (i + c.utf8Size)]
    simp only [blen_cons, Nat.add_assoc]
    rw [ite_eq_right (by simp only [String.Pos.Raw.le_iff]; omega)]

/-- Stepping back from the position which follows the character `d`. -/
theorem prev_eq {s : String} {pre rest : List Char} {d : Char}
    (h : s.toList = pre ++ d :: rest) :
    String.Pos.Raw.prev s ⟨blen pre + d.utf8Size⟩ = ⟨blen pre⟩ := by
  have := utf8PrevAux_append d rest pre 0
  simp only [Nat.zero_add] at this
  simpa [String.Pos.Raw.prev, h] using this

end ByteScan

/-! ## A name -/

namespace NEString

/-- Reading a name in place reads what reading it from the text of the
token read. -/
theorem ofRange?_eq {s : String} {pre mid rest : List Char}
    (h : s.toList = pre ++ mid ++ rest) :
    NEString.ofRange? s ⟨blen pre⟩ ⟨blen pre + blen mid⟩
      = NEString.ofString? (String.ofList mid) := by
  have hx : String.Pos.Raw.extract s ⟨blen pre⟩ ⟨blen pre + blen mid⟩ = String.ofList mid :=
    extract_eq h
  simp only [NEString.ofRange?, NEString.ofString?, hx]
  by_cases hz : (String.ofList mid).utf8ByteSize = 0
  · have he : String.ofList mid = "" := String.utf8ByteSize_eq_zero_iff.mp hz
    simp [he]
  · have he : String.ofList mid ≠ "" := fun he => hz (by rw [he]; rfl)
    simp [hz, he]

end NEString

/-! ## A string literal -/

namespace JSStringSrc

/-- A quote is one byte wide. -/
private theorem utf8Size_of_quote {c : Char} {q : QuoteKind} (h : QuoteKind.ofChar? c = some q) :
    c.utf8Size = 1 ∧ c = q.char := by
  unfold QuoteKind.ofChar? at h
  by_cases h1 : c == '\''
  · have : c = '\'' := by simpa using h1
    subst this
    simp only [h1, ite_eq_left] at h
    cases h
    exact ⟨by decide, by decide⟩
  · by_cases h2 : c == '"'
    · have : c = '"' := by simpa using h2
      subst this
      simp only [h1, h2, ite_eq_left, Bool.false_eq_true] at h
      cases h
      exact ⟨by decide, by decide⟩
    · simp [h1, h2] at h

/-- Reading a string literal in place reads what reading it from the text
of the token read. -/
theorem ofRange?_eq {s : String} {pre mid rest : List Char}
    (h : s.toList = pre ++ mid ++ rest) :
    JSStringSrc.ofRange? s ⟨blen pre⟩ ⟨blen pre + blen mid⟩
      = JSStringSrc.ofString? (String.ofList mid) := by
  have hlist : (String.ofList mid).toList = mid := String.toList_ofList
  have hsize : (String.ofList mid).utf8ByteSize = blen mid := by
    rw [← blen_toList, hlist]
  rcases List.eq_nil_or_concat mid with rfl | ⟨init, d, rfl⟩
  · simp [JSStringSrc.ofRange?, JSStringSrc.ofString?, hsize]
  · simp only [List.concat_eq_append] at h hlist hsize ⊢
    have hd := d.utf8Size_pos
    simp only [JSStringSrc.ofRange?, JSStringSrc.ofString?, hsize]
    cases init with
    | nil =>
      -- a literal of one character: the closing quote would be the opening one
      have h1 : s.toList = pre ++ d :: rest := by simpa using h
      have hprevL : String.Pos.Raw.prev s ⟨blen pre + blen ([] ++ [d])⟩ = ⟨blen pre⟩ := by
        simpa using prev_eq h1
      have h2 : (String.ofList ([] ++ [d])).toList = [] ++ d :: [] := by simp
      have hprevR : String.Pos.Raw.prev (String.ofList ([] ++ [d])) ⟨blen ([] ++ [d])⟩ = ⟨0⟩ := by
        simpa using prev_eq h2
      have hle : ¬ (blen pre + d.utf8Size ≤ blen pre) := by omega
      rw [hprevL, hprevR]
      rcases hq : QuoteKind.ofChar? (String.Pos.Raw.get s ⟨blen pre⟩) with _ | q <;>
        rcases hq' : QuoteKind.ofChar? (String.Pos.Raw.get (String.ofList ([] ++ [d])) ⟨0⟩) with
          _ | q' <;> simp [ite_self, hle]
    | cons c cs =>
      have hc := c.utf8Size_pos
      -- the first character
      have hgetL : String.Pos.Raw.get s ⟨blen pre⟩ = c :=
        get_eq (pre := pre) (suf := cs ++ [d] ++ rest) (by simpa using h)
      have hgetR : String.Pos.Raw.get (String.ofList ((c :: cs) ++ [d])) ⟨0⟩ = c :=
        get_eq (pre := []) (suf := cs ++ [d]) (by simp)
      -- stepping back from the end lands on the last character
      have hsplitL : s.toList = (pre ++ c :: cs) ++ d :: rest := by simpa using h
      have hprevL : String.Pos.Raw.prev s ⟨blen pre + blen ((c :: cs) ++ [d])⟩
          = ⟨blen pre + blen (c :: cs)⟩ := by
        have hp := prev_eq hsplitL
        rw [show blen pre + blen ((c :: cs) ++ [d]) = blen (pre ++ c :: cs) + d.utf8Size by
          simp; omega, hp]
        simp
      have hsplitR : (String.ofList ((c :: cs) ++ [d])).toList = (c :: cs) ++ d :: [] := by
        simp
      have hprevR : String.Pos.Raw.prev (String.ofList ((c :: cs) ++ [d]))
          ⟨blen ((c :: cs) ++ [d])⟩ = ⟨blen (c :: cs)⟩ := by
        have hp := prev_eq hsplitR
        rw [show blen ((c :: cs) ++ [d]) = blen (c :: cs) + d.utf8Size by
          simp only [blen_append, blen_cons, blen_nil]; omega, hp]
      -- the last character
      have hlastL : String.Pos.Raw.get s ⟨blen pre + blen (c :: cs)⟩ = d := by
        have hp := get_eq (s := s) (pre := pre ++ c :: cs) (suf := rest) (c := d) hsplitL
        rwa [show blen (pre ++ c :: cs) = blen pre + blen (c :: cs) by simp] at hp
      have hlastR : String.Pos.Raw.get (String.ofList ((c :: cs) ++ [d])) ⟨blen (c :: cs)⟩ = d :=
        get_eq (pre := c :: cs) (suf := []) hsplitR
      rw [hgetL, hgetR, hprevL, hprevR, hlastL, hlastR]
      rcases hq : QuoteKind.ofChar? c with _ | q
      · simp only [ite_self]
      · obtain ⟨hone, hqc⟩ := utf8Size_of_quote hq
        have hbodyL : String.Pos.Raw.extract s ⟨blen pre + 1⟩ ⟨blen pre + blen (c :: cs)⟩
            = String.ofList cs := by
          have hsp : s.toList = (pre ++ [c]) ++ cs ++ (d :: rest) := by simpa using h
          have hx := extract_eq hsp
          rw [show blen (pre ++ [c]) = blen pre + 1 by simp [hone]] at hx
          rw [show blen pre + blen (c :: cs) = blen pre + 1 + blen cs by
            simp [hone]; omega]
          exact hx
        have hbodyR : String.Pos.Raw.extract (String.ofList ((c :: cs) ++ [d])) ⟨1⟩
            ⟨blen (c :: cs)⟩ = String.ofList cs := by
          have hsp : (String.ofList ((c :: cs) ++ [d])).toList = [c] ++ cs ++ [d] := by
            simp
          have hx := extract_eq hsp
          rw [show blen [c] = 1 by simp [hone]] at hx
          rw [show blen (c :: cs) = 1 + blen cs by simp [hone]]
          exact hx
        simp only [hbodyL, hbodyR]
        have h1 : ¬ (blen pre + blen ((c :: cs) ++ [d]) ≤ blen pre) := by
          simp only [blen_append, blen_cons, blen_nil]; omega
        have h2 : ¬ (blen pre + blen (c :: cs) ≤ blen pre) := by
          simp only [blen_cons]; omega
        have h3 : ¬ ((blen ((c :: cs) ++ [d]) == 0) = true) := by
          simp only [blen_append, blen_cons, blen_nil, beq_iff_eq]; omega
        have h4 : ¬ ((blen (c :: cs) == 0) = true) := by
          simp only [blen_cons, beq_iff_eq]; omega
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]

end JSStringSrc

/-! ## A chunk of a template literal -/

namespace ByteScan

/-- Slicing an empty range gives the empty string. -/
theorem extract_empty (s : String) (b e : String.Pos.Raw) (h : e.byteIdx ≤ b.byteIdx) :
    String.Pos.Raw.extract s b e = "" := by
  simp only [String.Pos.Raw.extract]
  rw [ite_eq_left (by simpa [String.Pos.Raw.le_iff] using h)]

/-- A list occupies at least as many bytes as any of its prefixes. -/
theorem blen_le_of_prefix {p q : List Char} (h : p <+: q) : blen p ≤ blen q := by
  obtain ⟨t, rfl⟩ := h
  simp

/-- Two prefixes of the same list are comparable, so the shorter one is a
prefix of the longer one. -/
theorem prefix_of_blen_le {l p q : List Char} (hp : p <+: l) (hq : q <+: l)
    (h : blen p ≤ blen q) : p <+: q := by
  rcases List.prefix_or_prefix_of_prefix hp hq with hpq | hqp
  · exact hpq
  · have := blen_le_of_prefix hqp
    have : blen p = blen q := by omega
    obtain ⟨t, rfl⟩ := hqp
    have ht : blen t = 0 := by simp at this; omega
    have : t = [] := by
      cases t with
      | nil => rfl
      | cons a as =>
        have := a.utf8Size_pos
        simp only [blen_cons] at ht
        omega
    simp [this]

/-- Slicing the same segment out of the input and out of the text of the
token gives the same string. -/
theorem extract_transfer {s : String} {pre mid rest p q : List Char}
    (h : s.toList = pre ++ mid ++ rest) (hpq : p <+: q) (hq : q <+: mid) :
    String.Pos.Raw.extract s ⟨blen pre + blen p⟩ ⟨blen pre + blen q⟩
      = String.Pos.Raw.extract (String.ofList mid) ⟨blen p⟩ ⟨blen q⟩ := by
  obtain ⟨seg, rfl⟩ := hpq
  obtain ⟨tail, hmid⟩ := hq
  have hlist : (String.ofList mid).toList = mid := String.toList_ofList
  have hL : String.Pos.Raw.extract s ⟨blen pre + blen p⟩ ⟨blen pre + blen (p ++ seg)⟩
      = String.ofList seg := by
    have hs : s.toList = (pre ++ p) ++ seg ++ (tail ++ rest) := by
      rw [h, ← hmid]; simp
    have hx := extract_eq hs
    rw [show blen (pre ++ p) = blen pre + blen p by simp] at hx
    rw [show blen pre + blen (p ++ seg) = blen pre + blen p + blen seg by simp; omega]
    exact hx
  have hR : String.Pos.Raw.extract (String.ofList mid) ⟨blen p⟩ ⟨blen (p ++ seg)⟩
      = String.ofList seg := by
    have hs : (String.ofList mid).toList = p ++ seg ++ tail := by
      rw [hlist, ← hmid]
    have hx := extract_eq hs
    rw [show blen (p ++ seg) = blen p + blen seg by simp]
    exact hx
  rw [hL, hR]

end ByteScan

open Language.JavaScript.Parser.AST

namespace ByteScan

/-- What the reader returns once the two characters which can close the
chunk are known: it slices up to the `${`, up to the closing backquote, or
up to the end. -/
theorem templateChunkFrom_eval {raw : String} {b p q : Nat} {stop : String.Pos.Raw}
    {dc ec : Char} (hlt : b < stop.byteIdx)
    (hlast : String.Pos.Raw.prev raw stop = ⟨p⟩)
    (hbefore : String.Pos.Raw.prev raw ⟨p⟩ = ⟨q⟩)
    (hd : String.Pos.Raw.get raw ⟨p⟩ = dc)
    (he : String.Pos.Raw.get raw ⟨q⟩ = ec) :
    templateChunkFrom raw b stop
      = String.Pos.Raw.extract raw ⟨b⟩
          ⟨if b < p ∧ dc = '{' ∧ ec = '$' then q
           else if dc = '`' then p else stop.byteIdx⟩ := by
  unfold templateChunkFrom
  rw [ite_eq_right (by omega)]
  simp only [hlast, hbefore, hd, he, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    and_assoc]

/-- The same, when the chunk stops before the character which precedes the
last one, so that the `${` cannot be there. -/
theorem templateChunkFrom_eval_le {raw : String} {b p : Nat} {stop : String.Pos.Raw}
    {dc : Char} (hlt : b < stop.byteIdx) (hple : p ≤ b)
    (hlast : String.Pos.Raw.prev raw stop = ⟨p⟩)
    (hd : String.Pos.Raw.get raw ⟨p⟩ = dc) :
    templateChunkFrom raw b stop
      = String.Pos.Raw.extract raw ⟨b⟩ ⟨if dc = '`' then p else stop.byteIdx⟩ := by
  have hev := templateChunkFrom_eval (raw := raw) (b := b) (p := p)
    (q := (String.Pos.Raw.prev raw ⟨p⟩).byteIdx) (stop := stop) (dc := dc)
    (ec := String.Pos.Raw.get raw ⟨(String.Pos.Raw.prev raw ⟨p⟩).byteIdx⟩)
    hlt hlast rfl hd rfl
  rw [hev, ite_eq_right (fun hc => absurd hc.1 (by omega))]

end ByteScan

/-- Reading a chunk of a template literal in place, from a position inside
the token, reads what reading it from the text of the token read. -/
theorem templateChunkFrom_eq {s : String} {pre mid rest m1 m2 : List Char}
    (h : s.toList = pre ++ mid ++ rest) (hm : mid = m1 ++ m2) :
    templateChunkFrom s (blen pre + blen m1) ⟨blen pre + blen mid⟩
      = templateChunkFrom (String.ofList mid) (blen m1) ⟨blen mid⟩ := by
  have hlist : (String.ofList mid).toList = mid := String.toList_ofList
  have hm1 : m1 <+: mid := ⟨m2, hm.symm⟩
  have hm1le : blen m1 ≤ blen mid := blen_le_of_prefix hm1
  by_cases hstop : blen mid ≤ blen m1
  · -- nothing left to read
    simp only [templateChunkFrom]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  · -- the chunk is not empty, so it has a last character
    have hne : mid ≠ [] := by
      intro hnil; rw [hnil] at hstop; simp at hstop
    obtain ⟨init, d, rfl⟩ : ∃ init d, mid = init ++ [d] := by
      rcases List.eq_nil_or_concat mid with hnil | ⟨init, d, hid⟩
      · exact absurd hnil hne
      · exact ⟨init, d, by simpa using hid⟩
    have hd := d.utf8Size_pos
    have hblen : blen (init ++ [d]) = blen init + d.utf8Size := by simp
    -- stepping back from the end lands on the last character
    have hsplitL : s.toList = (pre ++ init) ++ d :: rest := by simpa using h
    have hlastL : String.Pos.Raw.prev s ⟨blen pre + blen (init ++ [d])⟩
        = ⟨blen pre + blen init⟩ := by
      have hp := prev_eq hsplitL
      rw [show blen pre + blen (init ++ [d]) = blen (pre ++ init) + d.utf8Size by
        simp only [blen_append, blen_cons, blen_nil]; omega, hp]
      simp
    have hsplitR : (String.ofList (init ++ [d])).toList = init ++ d :: [] := by simp
    have hlastR : String.Pos.Raw.prev (String.ofList (init ++ [d])) ⟨blen (init ++ [d])⟩
        = ⟨blen init⟩ := by
      have hp := prev_eq hsplitR
      rw [show blen (init ++ [d]) = blen init + d.utf8Size by simp, hp]
    have hgetdL : String.Pos.Raw.get s ⟨blen pre + blen init⟩ = d := by
      have hp := get_eq (s := s) (pre := pre ++ init) (suf := rest) (c := d) hsplitL
      rwa [show blen (pre ++ init) = blen pre + blen init by simp] at hp
    have hgetdR : String.Pos.Raw.get (String.ofList (init ++ [d])) ⟨blen init⟩ = d :=
      get_eq (pre := init) (suf := []) hsplitR
    by_cases hg : blen m1 < blen init
    · -- there is a character before the last one, so the chunk can end in `${`
      have hinitne : init ≠ [] := by
        intro hnil; rw [hnil] at hg; simp at hg
      obtain ⟨init2, e, rfl⟩ : ∃ init2 e, init = init2 ++ [e] := by
        rcases List.eq_nil_or_concat init with hnil | ⟨init2, e, hid⟩
        · exact absurd hnil hinitne
        · exact ⟨init2, e, by simpa using hid⟩
      have he := e.utf8Size_pos
      have hsplitL2 : s.toList = (pre ++ init2) ++ e :: ([d] ++ rest) := by simpa using h
      have hbeforeL : String.Pos.Raw.prev s ⟨blen pre + blen (init2 ++ [e])⟩
          = ⟨blen pre + blen init2⟩ := by
        have hp := prev_eq hsplitL2
        rw [show blen pre + blen (init2 ++ [e]) = blen (pre ++ init2) + e.utf8Size by
          simp only [blen_append, blen_cons, blen_nil]; omega, hp]
        simp
      have hsplitR2 : (String.ofList ((init2 ++ [e]) ++ [d])).toList
          = init2 ++ e :: [d] := by simp
      have hbeforeR : String.Pos.Raw.prev (String.ofList ((init2 ++ [e]) ++ [d]))
          ⟨blen (init2 ++ [e])⟩ = ⟨blen init2⟩ := by
        have hp := prev_eq hsplitR2
        rw [show blen (init2 ++ [e]) = blen init2 + e.utf8Size by simp, hp]
      have hgeteL : String.Pos.Raw.get s ⟨blen pre + blen init2⟩ = e := by
        have hp := get_eq (s := s) (pre := pre ++ init2) (suf := [d] ++ rest) (c := e) hsplitL2
        rwa [show blen (pre ++ init2) = blen pre + blen init2 by simp] at hp
      have hgeteR : String.Pos.Raw.get (String.ofList ((init2 ++ [e]) ++ [d]))
          ⟨blen init2⟩ = e := get_eq (pre := init2) (suf := [d]) hsplitR2
      -- `m1` stops before the last two characters
      have hm1init : m1 <+: init2 := by
        have hpre : m1 <+: init2 ++ [e] :=
          prefix_of_blen_le hm1 ⟨[d], by simp⟩ (Nat.le_of_lt hg)
        obtain ⟨t, ht⟩ := hpre
        have hblen1 : blen m1 + blen t = blen (init2 ++ [e]) := by rw [← ht]; simp
        have htne : t ≠ [] := by
          intro hnil
          rw [hnil] at hblen1
          simp only [blen_nil, Nat.add_zero] at hblen1
          omega
        obtain ⟨u, last, rfl⟩ : ∃ u last, t = u ++ [last] := by
          rcases List.eq_nil_or_concat t with hnil | ⟨u, last, hid⟩
          · exact absurd hnil htne
          · exact ⟨u, last, by simpa using hid⟩
        refine ⟨u, ?_⟩
        have ht' : (m1 ++ u) ++ [last] = init2 ++ [e] := by rw [← ht]; simp
        exact (List.append_inj' ht' (by simp)).1
      have hinit2pre : init2 <+: init2 ++ [e] ++ [d] := ⟨[e] ++ [d], by simp⟩
      have hinitpre : init2 ++ [e] <+: init2 ++ [e] ++ [d] := ⟨[d], by simp⟩
      rw [templateChunkFrom_eval
            (show blen pre + blen m1 < (⟨blen pre + blen (init2 ++ [e] ++ [d])⟩ :
              String.Pos.Raw).byteIdx by
              show blen pre + blen m1 < blen pre + blen (init2 ++ [e] ++ [d]); omega)
            hlastL hbeforeL hgetdL hgeteL,
          templateChunkFrom_eval
            (show blen m1 < (⟨blen (init2 ++ [e] ++ [d])⟩ : String.Pos.Raw).byteIdx by
              show blen m1 < blen (init2 ++ [e] ++ [d]); omega)
            hlastR hbeforeR hgetdR hgeteR]
      by_cases hbrace : d = '{' ∧ e = '$'
      · rw [ite_eq_left (⟨by omega, hbrace.1, hbrace.2⟩ :
              blen pre + blen m1 < blen pre + blen (init2 ++ [e]) ∧ d = '{' ∧ e = '$'),
            ite_eq_left (⟨hg, hbrace.1, hbrace.2⟩ :
              blen m1 < blen (init2 ++ [e]) ∧ d = '{' ∧ e = '$')]
        exact extract_transfer h hm1init hinit2pre
      · rw [ite_eq_right (show ¬ (blen pre + blen m1 < blen pre + blen (init2 ++ [e]) ∧ d = '{' ∧ e = '$')
              from fun hc => hbrace ⟨hc.2.1, hc.2.2⟩),
            ite_eq_right (show ¬ (blen m1 < blen (init2 ++ [e]) ∧ d = '{' ∧ e = '$')
              from fun hc => hbrace ⟨hc.2.1, hc.2.2⟩)]
        by_cases hbq : d = '`'
        · rw [ite_eq_left hbq, ite_eq_left hbq]
          exact extract_transfer h (prefix_of_blen_le hm1 hinitpre (Nat.le_of_lt hg)) hinitpre
        · rw [ite_eq_right hbq, ite_eq_right hbq]
          exact extract_transfer h hm1 (List.prefix_refl _)
    · -- the last character is the only one after `m1`
      rw [templateChunkFrom_eval_le
            (show blen pre + blen m1 < (⟨blen pre + blen (init ++ [d])⟩ :
              String.Pos.Raw).byteIdx by
              show blen pre + blen m1 < blen pre + blen (init ++ [d]); omega)
            (by omega) hlastL hgetdL,
          templateChunkFrom_eval_le
            (show blen m1 < (⟨blen (init ++ [d])⟩ : String.Pos.Raw).byteIdx by
              show blen m1 < blen (init ++ [d]); omega)
            (by omega) hlastR hgetdR]
      by_cases hbq : d = '`'
      · rw [ite_eq_left hbq, ite_eq_left hbq,
          extract_empty _ _ _ (show blen pre + blen init ≤ blen pre + blen m1 by omega),
          extract_empty _ _ _ (show blen init ≤ blen m1 by omega)]
      · rw [ite_eq_right hbq, ite_eq_right hbq]
        exact extract_transfer h hm1 (List.prefix_refl _)

/-- Slicing an empty range: the reader returns the empty string, whether or
not the range opens with a backquote. -/
theorem templateChunkRange_empty (raw : String) (b stop : String.Pos.Raw)
    (h : stop.byteIdx ≤ b.byteIdx) : templateChunkRange raw b stop = "" := by
  unfold templateChunkRange templateChunkFrom
  split <;> (try rw [ite_eq_left (by omega)]) <;> rfl

/-- What the reader does with the backquote which opens the head of a
template literal: it skips it, and reads on. -/
theorem templateChunkRange_eval {raw : String} {b : Nat} {stop : String.Pos.Raw} {c : Char}
    (hlt : b < stop.byteIdx) (hget : String.Pos.Raw.get raw ⟨b⟩ = c) :
    templateChunkRange raw ⟨b⟩ stop
      = templateChunkFrom raw (if c = '`' then b + 1 else b) stop := by
  unfold templateChunkRange
  simp only [hget, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  by_cases hbq : c = '`'
  · rw [ite_eq_left ⟨hlt, hbq⟩, ite_eq_left hbq]
  · rw [ite_eq_right (fun hc => hbq hc.2), ite_eq_right hbq]

/-- Reading a chunk of a template literal in place reads what reading it
from the text of the token read. -/
theorem templateChunkRange_eq {s : String} {pre mid rest : List Char}
    (h : s.toList = pre ++ mid ++ rest) :
    templateChunkRange s ⟨blen pre⟩ ⟨blen pre + blen mid⟩
      = templateChunk (String.ofList mid) := by
  have hlist : (String.ofList mid).toList = mid := String.toList_ofList
  have hsize : (String.ofList mid).utf8ByteSize = blen mid := by
    rw [← blen_toList, hlist]
  cases mid with
  | nil =>
    rw [templateChunkRange_empty _ _ _
          (show blen pre + blen ([] : List Char) ≤ blen pre by simp),
        templateChunk,
        templateChunkRange_empty (String.ofList ([] : List Char)) ⟨0⟩
          ⟨(String.ofList ([] : List Char)).utf8ByteSize⟩
          (show (String.ofList ([] : List Char)).utf8ByteSize ≤ 0 by simp [hsize])]
  | cons c cs =>
    have hc := c.utf8Size_pos
    have hpos : 0 < blen (c :: cs) := by simp only [blen_cons]; omega
    have hgetL : String.Pos.Raw.get s ⟨blen pre⟩ = c :=
      get_eq (pre := pre) (suf := cs ++ rest) (by simpa using h)
    have hgetR : String.Pos.Raw.get (String.ofList (c :: cs)) ⟨0⟩ = c :=
      get_eq (pre := []) (suf := cs) (by simp)
    simp only [templateChunk, hsize]
    rw [templateChunkRange_eval
          (show blen pre < (⟨blen pre + blen (c :: cs)⟩ : String.Pos.Raw).byteIdx by
            show blen pre < blen pre + blen (c :: cs); omega) hgetL,
        templateChunkRange_eval
          (show 0 < (⟨blen (c :: cs)⟩ : String.Pos.Raw).byteIdx by
            show 0 < blen (c :: cs); omega) hgetR]
    by_cases hbq : c = '`'
    · have hone : c.utf8Size = 1 := by rw [hbq]; decide
      have hEq := templateChunkFrom_eq (m1 := [c]) (m2 := cs) h rfl
      rw [ite_eq_left hbq, ite_eq_left hbq]
      simp only [blen_cons, blen_nil, hone, Nat.add_zero, Nat.zero_add] at hEq ⊢
      exact hEq
    · have hEq := templateChunkFrom_eq (m1 := ([] : List Char)) (m2 := c :: cs) h rfl
      rw [ite_eq_right hbq, ite_eq_right hbq]
      simpa using hEq

end Language.JavaScript
