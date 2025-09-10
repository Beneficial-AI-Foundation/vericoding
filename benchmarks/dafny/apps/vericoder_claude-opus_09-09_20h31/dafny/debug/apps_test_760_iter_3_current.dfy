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
lemma TandemRepeatProperties(s: seq<char>, i: int, n: int)
    requires 0 <= i < |s|
    requires 2 <= n <= |s| - i
    requires n % 2 == 0
    ensures is_tandem_repeat(s[i..i+n]) ==> n % 2 == 0
{
}

lemma SubstringBounds(s: seq<char>, i: int, n: int)
    requires 0 <= i < |s|
    requires 2 <= n <= |s| - i
    ensures i + n <= |s|
    ensures i >= 0
    ensures |s[i..i+n]| == n
{
}

lemma TandemRepeatMax(extended: seq<char>, i: int, max_length: int)
    requires 0 <= i <= |extended|
    requires max_length >= 0
    requires max_length % 2 == 0
    requires max_length <= |extended|
    requires forall ii, nn :: 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 && 
            is_tandem_repeat(extended[ii..ii+nn]) ==> nn <= max_length
    ensures forall ii, nn :: 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 && 
            is_tandem_repeat(extended[ii..ii+nn]) ==> nn <= max_length
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
    var max_length := 0;
    
    var i := 0;
    while i < |extended|
        invariant 0 <= i <= |extended|
        invariant max_length >= 0
        invariant max_length % 2 == 0
        invariant max_length <= |extended|
        invariant forall ii, nn | 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 :: 
                is_tandem_repeat(extended[ii..ii+nn]) ==> nn <= max_length
        invariant max_length == 0 ==> forall ii, nn | 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 :: 
                !is_tandem_repeat(extended[ii..ii+nn])
        invariant max_length > 0 ==> exists ii, nn | 0 <= ii < |extended| && 2 <= nn <= |extended| - ii && nn % 2 == 0 :: 
                is_tandem_repeat(extended[ii..ii+nn]) && nn == max_length
    {
        var n := 2;
        while n <= |extended| - i && n % 2 == 0
            invariant 2 <= n <= |extended| - i + 2
            invariant n % 2 == 0
            invariant max_length >= 0
            invariant max_length % 2 == 0
            invariant max_length <= |extended|
            invariant forall ii, nn | 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 :: 
                    is_tandem_repeat(extended[ii..ii+nn]) ==> nn <= max_length
            invariant forall nn | 2 <= nn < n && nn % 2 == 0 && nn <= |extended| - i :: 
                    is_tandem_repeat(extended[i..i+nn]) ==> nn <= max_length
            invariant max_length == 0 ==> forall ii, nn | 0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 :: 
                    !is_tandem_repeat(extended[ii..ii+nn])
            invariant max_length == 0 ==> forall nn | 2 <= nn < n && nn % 2 == 0 && nn <= |extended| - i :: 
                    !is_tandem_repeat(extended[i..i+nn])
            invariant max_length > 0 ==> exists ii, nn | 0 <= ii < |extended| && 2 <= nn <= |extended| - ii && nn % 2 == 0 :: 
                    is_tandem_repeat(extended[ii..ii+nn]) && nn == max_length
            decreases |extended| - i - n + 2
        {
            SubstringBounds(extended, i, n);
            
            if is_tandem_repeat(extended[i..i+n]) {
                if n > max_length {
                    max_length := n;
                }
            }
            n := n + 2;
        }
        i := i + 1;
    }
    
    result := max_length;
}
// </vc-code>

