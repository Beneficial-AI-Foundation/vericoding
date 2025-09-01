

// <vc-helpers>
lemma lemma_i_le_k_or_prime(k: int, i: int)
  requires 2 <= i
  requires i*i > k
  requires forall j :: 2 <= j < i ==> k % j != 0
  ensures forall x :: 2 <= x < k ==> k % x != 0
{
  if i > k
  {
      forall x | 2 <= x < k proves k % x != 0
      {
          assert x < i;
          assert k%x != 0;
      }
  }
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if k == 2 then return true;
  if k % 2 == 0 then return false;
  var i := 3;
  while i * i <= k
    invariant 2 <= i <= k
    invariant i % 2 == 1 // i is always odd
    invariant forall j :: 2 <= j < i && j % 2 == 1 ==> k % j != 0
  {
    if k % i == 0 then
      return false;
    i := i + 2;
  }
  lemma_i_le_k_or_prime(k, i);
  return true;
}
// </vc-code>

