method main(n: int, k: int) returns (k_out: int)
    requires n > 0;
    requires k > n;
    ensures k_out >= 0;
// </vc-spec>
// <vc-code>
{
  k_out := k;
}
// </vc-code>