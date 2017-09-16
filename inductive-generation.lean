import .monotone

open set

lemma boolean_algebras_equal {α} {f g : boolean_algebra α} (h : f.contains = g.contains) : f = g :=
begin
    induction f with f_contains,
    induction g with g_contains,
    dsimp at h,
    subst h
end

inductive generate_sets { α } (X : set (set α)) : set α → Prop
| basic  : ∀s∈X, generate_sets s
| univ   : generate_sets univ
| complements : ∀ s, generate_sets s → generate_sets (compl s)
| unions  : ∀s t, generate_sets s → generate_sets t → generate_sets (s ∪ t)

definition boolean_algebra_generated_by { α } ( X : set (set α) ) : boolean_algebra α :=
{ boolean_algebra .
  contains          := generate_sets X,
  contains_universe := generate_sets.univ X,
  complements       := generate_sets.complements,
  unions            := generate_sets.unions
}

lemma two_descriptions_of_boolean_algebra_agree { α } { X : set (set α)} :  coarsest_boolean_algebra_containing X = boolean_algebra_generated_by X :=
begin
  apply boolean_algebras_equal,
  dsimp {unfold_reducible := tt, md := semireducible},
  apply funext,
  intros,
  -- I have no idea how to do this!
  admit
end
