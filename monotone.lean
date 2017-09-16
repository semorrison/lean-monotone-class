import tidy.tidy
import data.set

open set


structure boolean_algebra ( α : Type ) :=
  ( contains : set (set α) )
  ( contains_universe : contains univ )
  ( complements : ∀ { s : set α }, contains s → contains (compl s) )
  ( unions : ∀ { s t : set α }, contains s → contains t → contains (s ∪ t) )

definition intersection_of_boolean_algebras { α β : Type } ( algebras : α → boolean_algebra β ) : boolean_algebra β :=
{
  contains          := λ s, ∀ a : α, (algebras a).contains s,
  contains_universe := begin intro a, exact (algebras a).contains_universe, end,
  complements       := begin intro s, intro f, intro a, exact (algebras a).complements (f a) end,
  unions            := begin intros s t, intros f g, intro a, exact (algebras a).unions (f a) (g a) end 
}

definition boolean_algebra_coarser { α } ( B C : boolean_algebra α ) := C.contains ⊆ B.contains

structure boolean_algebra_containing { α } ( X : set (set α) ) := 
  ( algebra    : boolean_algebra α )
  ( containing : ∀ s ∈ X, algebra.contains s )

definition coarsest_boolean_algebra_containing { α } ( X : set (set α) ) : boolean_algebra α :=
intersection_of_boolean_algebras (@boolean_algebra_containing.algebra _ X)

definition countable_union        { α : Type } (f : ℕ → set α) : set α := (λ a : α, ∃ n : ℕ, a ∈ (f n))
definition countable_intersection { α : Type } (f : ℕ → set α) : set α := (λ a : α, ∀ n : ℕ, a ∈ (f n))

lemma complement_of_countable_union_as_countable_intersection { α } (f: ℕ → set α) : compl (countable_union f) = countable_intersection (compl ∘ f) :=
begin
  unfold countable_union countable_intersection set.compl,
  apply funext,
  intros x,
  dsimp',
  unfold set.mem set.compl,
  dsimp',
  apply propext,
  split,
  {
    intros,
    exact a ⟨ n, a_1 ⟩,
  },
  {
    intros,
    apply exists.elim a_1 a, 
  }
end

lemma countable_union_of_complements_as_subset { α } (f: ℕ → set α) : countable_union (compl ∘ f) ⊆ compl (countable_intersection f) :=
begin
  unfold countable_union countable_intersection set.compl,
  intros x,
  dsimp',
  unfold set.mem set.compl,
  dsimp',
  intros,
  have p : ∀ n, ((f n x) → false) → false,
  intros n,
  exact non_contradictory_intro (a_1 n),
  apply exists.elim a p, 
end


structure sigma_algebra ( α : Type ) extends boolean_algebra α :=
  ( countable_unions        : ∀ { f : ℕ → set α }, (Π n : ℕ, contains (f n)) → contains (countable_union        f) )
  ( countable_intersections : ∀ { f : ℕ → set α }, (Π n : ℕ, contains (f n)) → contains (countable_intersection f) )

-- It requires classical logic, apparently, do deduce countable intersections from countable unions.

structure is_sigma_algebra { α } ( contains : set (set α ) ) :=
  ( sigma_algebra : sigma_algebra α )
  ( witness : sigma_algebra.contains = contains )

definition intersection_of_sigma_algebras { α β : Type } ( algebras : α → sigma_algebra β ) : sigma_algebra β :=
{ @intersection_of_boolean_algebras α β (λ a, (algebras a).to_boolean_algebra) with
  countable_unions := begin
                        intros s w, 
                        intro a, 
                        tidy,
                        let v := λ n, w n a,
                        exact (algebras a).countable_unions v,
                      end, 
  countable_intersections := begin
                        intros s w, 
                        intro a, 
                        tidy,
                        let v := λ n, w n a,
                        exact (algebras a).countable_intersections v,
                      end 
}

structure sigma_algebra_containing { α } ( X : set (set α) ) := 
  ( algebra    : sigma_algebra α )
  ( containing : ∀ s ∈ X, algebra.contains s )

definition coarsest_sigma_algebra_containing { α } ( X : set (set α) ) : sigma_algebra α :=
intersection_of_sigma_algebras (@sigma_algebra_containing.algebra _ X)

lemma coarsest_sigma_algebra_contains_generators { α } ( X : set (set α) ) : X ⊆ (coarsest_sigma_algebra_containing X).contains :=
begin
  tidy,
  unfold set.subset,
  tidy,
  unfold set.mem,
  tidy,
  have p := a_2.containing a a_1,
  tidy
end

lemma sigma_algebra_containing_contains_coarsest_sigma_algebra_containing 
  { α } 
  ( X : set (set α) ) 
  ( m : sigma_algebra α ) 
  ( w : X ⊆ m.contains ) 
  : (coarsest_sigma_algebra_containing X).contains ⊆ m.contains :=
begin
  tidy,
  unfold set.subset,
  intros Y,
  intros p,
  tidy,
  unfold set.mem at p,
  let c : sigma_algebra_containing X := ⟨ m, ♯ ⟩,
  let q := p c,
  tidy,
end

structure decreasing_sequence ( α : Type ) := 
  ( sets : ℕ → set α )
  ( decreasing : ∀ n : ℕ, (sets (n+1)) ⊆ (sets n) )

definition countable_decreasing_intersection { α } ( f: decreasing_sequence α ) : set α := countable_intersection f.sets

structure increasing_sequence ( α : Type ) := 
  ( sets : ℕ → set α )
  ( decreasing : ∀ n : ℕ, (sets n) ⊆ (sets (n+1)) )

definition countable_increasing_union { α } ( f: increasing_sequence α ) : set α := countable_union f.sets

structure monotone_class ( α : Type ) :=
  ( contains : set (set α) )
  ( countable_decreasing_intersections : ∀ f : decreasing_sequence α, (Π n : ℕ, contains (f.sets n)) → contains (countable_decreasing_intersection f)) 
  ( countable_increasing_unions        : ∀ f : increasing_sequence α, (Π n : ℕ, contains (f.sets n)) → contains (countable_increasing_union        f))

structure is_monotone_class { α } ( contains : set (set α ) ) :=
  ( monotone_class : monotone_class α )
  ( witness : monotone_class.contains = contains )

definition intersection_of_monotone_classes { α β : Type } ( classes : α → monotone_class β ) : monotone_class β :=
{ 
  contains          := λ s, ∀ a : α, (classes a).contains s,
  countable_decreasing_intersections := begin
                                          intros f w a,
                                          let v := λ n, w n a,
                                          exact (classes a).countable_decreasing_intersections f v,
                                        end,
  countable_increasing_unions        := begin
                                          intros f w a,
                                          let v := λ n, w n a,
                                          exact (classes a).countable_increasing_unions f v,
                                        end
}

definition monotone_class_coarser { α } ( B C : monotone_class α ) := C.contains ⊆ B.contains

structure monotone_class_containing { α } ( X : set (set α) ) := 
  ( monotone_class      : monotone_class α )
  ( containing : ∀ s ∈ X, monotone_class.contains s )

definition coarsest_monotone_class_containing { α } ( X : set (set α) ) : monotone_class α :=
intersection_of_monotone_classes (@monotone_class_containing.monotone_class _ X)

lemma coarsest_monotone_class_contains_generators { α } ( X : set (set α) ) : X ⊆ (coarsest_monotone_class_containing X).contains :=
begin
  tidy,
  unfold set.subset,
  tidy,
  unfold set.mem,
  tidy,
  have p := a_2.containing a a_1,
  tidy
end

lemma monotone_class_containing_contains_coarsest_monotone_class_containing
  { α } 
  ( X : set (set α) ) 
  ( m : monotone_class α ) 
  ( w : X ⊆ m.contains ) 
  : (coarsest_monotone_class_containing X).contains ⊆ m.contains :=
begin
  tidy,
  unfold set.subset,
  intros Y,
  intros p,
  tidy,
  unfold set.mem at p,
  let c : monotone_class_containing X := ⟨ m, ♯ ⟩,
  let q := p c,
  tidy,
end

definition monotone_class.complement { α } ( M : monotone_class α ) : monotone_class α := {
  contains := λ s, M.contains (- s),
  countable_decreasing_intersections := begin
                                          intros f w,
                                          admit,
                                        end,
  countable_increasing_unions        := sorry
}

lemma monotone_class_generated_by_a_boolean_algebra_equals_its_complement { α } ( B : boolean_algebra α ) : (coarsest_monotone_class_containing B.contains).contains = (coarsest_monotone_class_containing B.contains).complement.contains :=
begin
  apply subset.antisymm,
  {
    -- FIXME apply is sad :-( Why can't it infer the arguments?
    apply monotone_class_containing_contains_coarsest_monotone_class_containing
      B.contains
      (monotone_class.complement (coarsest_monotone_class_containing (B.contains))),
    tidy,
    unfold set.subset,
    intros s w,
    tidy,
    unfold set.mem,
    unfold set.mem at w,
    intros M,
    apply M.containing,
    exact B.complements w
  },
  {
    -- but how do we do this?
    admit
  }
end

lemma monotone_class_generated_by_a_boolean_algebra_is_a_sigma_algebra 
  { α } 
  ( B : boolean_algebra α ) 
  : is_sigma_algebra (coarsest_monotone_class_containing B.contains).contains :=
begin
  fsplit,
  fsplit,
  fsplit,
  { 
    -- first we specify the underlying family of sets
    exact (coarsest_monotone_class_containing B.contains).contains,
  },
  {
    -- the universe is in the monotone class because it is in the boolean algebra
    apply coarsest_monotone_class_contains_generators,
    exact B.contains_universe,
  },
  {
    -- contains complements?
    admit,
  },
  admit,
  admit,
  admit,
  admit,
end
  
lemma sigma_algebra_generated_by_a_boolean_algebra_is_a_monotone_class 
  { α } 
  ( B : boolean_algebra α ) 
  : is_monotone_class (coarsest_sigma_algebra_containing B.contains).contains :=
begin
  let M := coarsest_sigma_algebra_containing B.contains,
  fsplit,
  fsplit,
  {
    exact M.contains,
  },
  {
    -- decreasing intersections
    have c := M.countable_intersections,
    intros f n w,
    exact c n w,
  },
  {
    -- increasing unions
    have c := M.countable_unions,
    intros f n w,
    exact c n w,
  },
  tidy,
end

private lemma monotone_class_generated_by_a_boolean_algebra_as_a_sigma_algebra  { α } ( B : boolean_algebra α ) : (coarsest_monotone_class_containing (B.contains)).contains = (monotone_class_generated_by_a_boolean_algebra_is_a_sigma_algebra B).sigma_algebra.contains :=
begin
  rewrite (monotone_class_generated_by_a_boolean_algebra_is_a_sigma_algebra B).witness,
end
private lemma sigma_algebra_generated_by_a_boolean_algebra_as_a_monotone_class  { α } ( B : boolean_algebra α ) : (coarsest_sigma_algebra_containing (B.contains)).contains = (sigma_algebra_generated_by_a_boolean_algebra_is_a_monotone_class B).monotone_class.contains :=
begin
  rewrite (sigma_algebra_generated_by_a_boolean_algebra_is_a_monotone_class B).witness,
end

theorem monotone_class_lemma 
  { α } 
  ( B : boolean_algebra α ) 
  : (coarsest_sigma_algebra_containing B.contains).contains = (coarsest_monotone_class_containing B.contains).contains :=
begin
  apply subset.antisymm,
  {
    rewrite monotone_class_generated_by_a_boolean_algebra_as_a_sigma_algebra,
    -- FIXME why does unification fail without specifying arguments?
    apply sigma_algebra_containing_contains_coarsest_sigma_algebra_containing
      B.contains
      ((monotone_class_generated_by_a_boolean_algebra_is_a_sigma_algebra B).sigma_algebra),
    rewrite ← monotone_class_generated_by_a_boolean_algebra_as_a_sigma_algebra,
    apply coarsest_monotone_class_contains_generators B.contains
  },
  {
    rewrite sigma_algebra_generated_by_a_boolean_algebra_as_a_monotone_class,
    -- FIXME
    apply monotone_class_containing_contains_coarsest_monotone_class_containing 
      B.contains 
      ((sigma_algebra_generated_by_a_boolean_algebra_is_a_monotone_class B).monotone_class),
    rewrite ← sigma_algebra_generated_by_a_boolean_algebra_as_a_monotone_class,
    apply coarsest_sigma_algebra_contains_generators B.contains
  }
end