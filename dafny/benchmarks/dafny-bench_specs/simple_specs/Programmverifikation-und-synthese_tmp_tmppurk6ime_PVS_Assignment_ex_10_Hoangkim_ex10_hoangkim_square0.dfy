// SPEC
//Problem01
method square0(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
}

/*
3 Verification conditions

1. VC1: Precondiotion implies the loop variant
n ∈ ℕ => sqn = 0*0 ∧ i = 0 ∧ x=? ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ i = 0 ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ 0 ≤ n 
2. VC2: Loop invariant and loop guard preserve the loop invariant.
VC2: i < n ∧ i+1 ≤ n ∧ sqn = i * i ⇒ sqn = sqn + x ∧ i = i + 1 ∧ x = 2 * i + 1
3.VC3: Loop terminates, and the loop invariant implies the postcondition.
VC3: ¬(i < n) ∧ i ≤ n ∧ sqn = i * i ⇒ sqn = n * n

Simplified VC for square0
1. true, since 0 = 0 and n >= 0 => 0 ≤ n
2. true, i < n => i + 1 <= n
3. true, ¬(i < n) ∧ i ≤ n ∧ sqn = i * i ⇒ sqn = n * n since ¬(i < n) ∧ i ≤ n imply i = n

*/
