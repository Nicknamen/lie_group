import tactic.default

theorem addition_of_natural_numbers_is_commutative (m n : ℕ) :
  m + n = n + m :=
begin
  induction n with d hd,
  {
    ring,
  },
  {
    ring,
  }
end