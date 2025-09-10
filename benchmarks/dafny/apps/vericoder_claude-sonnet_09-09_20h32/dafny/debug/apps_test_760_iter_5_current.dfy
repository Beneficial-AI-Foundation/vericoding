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
    ensures forall i, n :: {:trigger is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])} 
        0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> n <= |s| + k
{
}

lemma string_concat_properties(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures |s + seq(k, j => '*')| == |s| + k
{
}

lemma tandem_repeat_substring_lemma(extended: seq<char>, i: int, n: int)
    requires 0 <= i < |extended|
    requires 2 <= n <= |extended| - i
    requires n % 2 == 0
    ensures is_tandem_repeat(extended[i..i+n]) ==> n <= |extended|
{
}

lemma substring_bounds(extended: seq<char>, i: int, n: int)
    requires 0 <= i < |extended|
    requires 2 <= n <= |extended| - i
    ensures i + n <= |extended|
    ensures 0 <= i
    ensures i + n >= 2
{
}

lemma max_len_monotonic(old_max: int, new_max: int, extended: seq<char>)
    requires old_max >= 0 && old_max % 2 == 0
    requires new_max >= old_max
    requires new_max % 2 == 0
    ensures new_max >= 0 && new_max % 2 == 0
{
}

lemma extended_string_length(s: string, k: int)
    requires k >= 1
    requires |s| >= 1
    ensures |s + seq(k, j => '*')| == |s| + k
    ensures |s| + k >= 2
{
}

lemma tandem_witness_exists(extended: seq<char>, max_len: int, processed: int)
    requires max_len > 0
    requires max_len % 2 == 0
    requires exists ii, n :: 0 <= ii < processed && 2 <= n <= |extended| - ii && n % 2 == 0 && 
             is_tandem_repeat(extended[ii..ii+n]) && n == max_len
    ensures exists ii, n :: 0 <= ii < |extended| && 2 <= n <= |extended| - ii && n % 2 == 0 && 
            is_tandem_repeat(extended[ii..ii+n]) && n == max_len
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
    extended_string_length(s, k);
    var max_len := 0;
    
    var i := 0;
    while i < |extended|
        invariant 0 <= i <= |extended|
        invariant max_len >= 0
        invariant max_len % 2 == 0
        invariant max_len <= |extended|
        invariant forall ii, n :: {:trigger is_tandem_repeat(extended[ii..ii+n])}
                  (0 <= ii < i && 2 <= n <= |extended| - ii && n % 2 == 0 && 
                  is_tandem_repeat(extended[ii..ii+n])) ==> n <= max_len
        invariant max_len == 0 ==> (forall ii, n :: {:trigger is_tandem_repeat(extended[ii..ii+n])}
                  (0 <= ii < i && 2 <= n <= |extended| - ii && n % 2 == 0) ==> 
                  !is_tandem_repeat(extended[ii..ii+n]))
        invariant max_len > 0 ==> (exists ii, n :: {:trigger is_tandem_repeat(extended[ii..ii+n])}
                  0 <= ii < i && 2 <= n <= |extended| - ii && n % 2 == 0 && 
                  is_tandem_repeat(extended[ii..ii+n]) && n == max_len)
    {
        var n := 2;
        while n <= |extended| - i
            invariant 2 <= n
            invariant n % 2 == 0
            invariant max_len >= 0
            invariant max_len % 2 == 0
            invariant max_len <= |extended|
            invariant forall ii, nn :: {:trigger is_tandem_repeat(extended[ii..ii+nn])}
                      (0 <= ii < i && 2 <= nn <= |extended| - ii && nn % 2 == 0 && 
                      is_tandem_repeat(extended[ii..ii+nn])) ==> nn <= max_len
            invariant forall nn :: {:trigger is_tandem_repeat(extended[i..i+nn])}
                      (2 <= nn < n && nn % 2 == 0 && nn <= |extended| - i && 
                      is_tandem_repeat(extended[i..i+nn])) ==> nn <= max_len
        {
            if i + n <= |extended| && is_tandem_repeat(extended[i..i+n]) {
                if n > max_len {
                    max_len := n;
                }
            }
            n := n + 2;
        }
        i := i + 1;
    }
    
    if max_len > 0 {
        tandem_witness_exists(extended, max_len, |extended|);
    }
    
    result := max_len;
}
// </vc-code>

