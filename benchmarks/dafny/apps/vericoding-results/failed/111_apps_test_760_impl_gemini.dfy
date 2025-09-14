function is_tandem_repeat(s: seq<char>): bool
{
    if |s| % 2 != 0 then false
    else
        var half_len := |s| / 2;
        var first_half := s[0..half_len];
        var second_half := s[half_len..];
        forall i :: 0 <= i < half_len ==> 
            (first_half[i] == '*' || second_half[i] == '*' || first_half[i] == second_half[i])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: int)
    requires k >= 1
    requires |s| >= 1
    ensures result >= 0
    ensures result % 2 == 0
    ensures result <= |s| + k
    ensures forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) ==> n <= result
    ensures result == 0 ==> forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> 
            !is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])
    ensures result > 0 ==> exists i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            (is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) && n == result)
// </vc-spec>
// <vc-code>
{
    var extended_s := s + seq(k, j => '*');
    var N := |extended_s|;

    var n := if N % 2 == 0 then N else N - 1;

    while n >= 2
        invariant extended_s == s + seq(k, j => '*')
        invariant N == |s| + k
        invariant n % 2 == 0
        invariant 0 <= n <= N
        invariant forall l, i :: n < l <= N && l % 2 == 0 && 0 <= i <= N-l
                                ==> !is_tandem_repeat(extended_s[i..i+l])
    {
        var i := 0;
        while i <= N - n
            invariant 0 <= i <= N - n + 1
            invariant forall l, j :: (l == n && 0 <= j < i) || (n < l <= N && l % 2 == 0 && 0 <= j <= N-l)
                                    ==> !is_tandem_repeat(extended_s[j..j+l])
        {
            if is_tandem_repeat(extended_s[i..i+n]) {
                return n;
            }
            i := i + 1;
        }
        n := n - 2;
    }
// </vc-code>

