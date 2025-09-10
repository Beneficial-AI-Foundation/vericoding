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
lemma tandem_repeat_properties(s: seq<char>)
    ensures is_tandem_repeat(s) ==> |s| % 2 == 0
    ensures |s| % 2 != 0 ==> !is_tandem_repeat(s)
{
}

lemma max_tandem_repeat_bound(s: seq<char>, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> n <= |s| + k
{
}

lemma string_concat_properties(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures |s + seq(k, j => '*')| == |s| + k
{
}
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
    var extended := s + seq(k, j => '*');
    var max_len := 0;
    
    var i := 0;
    while i < |extended|
        invariant 0 <= i <= |extended|
        invariant max_len >= 0
        invariant max_len % 2 == 0
        invariant max_len <= |extended|
        invariant forall ii, n :: 0 <= ii < i && 2 <= n <= |extended| - ii && n % 2 == 0 && 
                  is_tandem_repeat(extended[ii..ii+n]) ==> n <= max_len
        invariant max_len == 0 ==> forall ii, n :: 0 <= ii < i && 2 <= n <= |extended| - ii && n % 2 == 0 ==> 
                  !is_tandem_repeat(extended[ii..ii+n])
        invariant max_len > 0 ==> exists ii, n :: 0 <= ii < i && 2 <= n <= |extended| - ii && n % 2 == 0 && 
                  is_tandem_repeat(extended[ii..ii+n]) && n == max_len
    {
        var n := 2;
        while n <= |extended| - i && n % 2 == 0
            invariant 2 <= n
            invariant n % 2 == 0
            invariant max_len >= 0
            invariant max_len % 2 == 0
            invariant max_len <= |extended|
            invariant forall ii, nn :: 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 && 
                      is_tandem_repeat(extended[ii..ii+nn]) ==> nn <= max_len
            invariant forall nn :: 2 <= nn < n && nn % 2 == 0 && nn <= |extended| - i && 
                      is_tandem_repeat(extended[i..i+nn]) ==> nn <= max_len
            invariant max_len == 0 ==> (forall ii, nn :: 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 ==> 
                      !is_tandem_repeat(extended[ii..ii+nn])) &&
                      (forall nn :: 2 <= nn < n && nn % 2 == 0 && nn <= |extended| - i ==> 
                      !is_tandem_repeat(extended[i..i+nn]))
        {
            if is_tandem_repeat(extended[i..i+n]) {
                if n > max_len {
                    max_len := n;
                }
            }
            n := n + 2;
        }
        i := i + 1;
    }
    
    result := max_len;
}
// </vc-code>

