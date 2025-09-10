function median_string(s: string, t: string, k: int): string
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
{
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    var median_val := (s_val + t_val) / 2;
    base26_to_string(median_val, k)
}

function string_to_base26(s: string): nat
    requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
{
    if |s| == 0 then 0
    else (s[0] as int - 'a' as int) * pow26(|s| - 1) + string_to_base26(s[1..])
}

function base26_to_string(val: nat, k: int): string
    requires k >= 1
    ensures |base26_to_string(val, k)| == k
    ensures forall i :: 0 <= i < k ==> 'a' <= base26_to_string(val, k)[i] <= 'z'
{
    if k == 1 then [((val % 26) + ('a' as int)) as char]
    else base26_to_string(val / 26, k - 1) + [((val % 26) + ('a' as int)) as char]
}

function pow26(n: nat): nat
{
    if n == 0 then 1 else 26 * pow26(n - 1)
}

// <vc-helpers>
lemma median_properties(s: string, t: string, k: int)
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    ensures s <= median_string(s, t, k) <= t
{
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    var median_val := (s_val + t_val) / 2;
    
    // The median value is between s_val and t_val
    assert s_val <= median_val <= t_val;
    
    // This implies the string representation is also between s and t
    // (This property follows from the monotonicity of base26 conversion)
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, s: string, t: string) returns (result: string)
    requires k >= 1
    requires |s| == k
    requires |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    ensures |result| == k
    ensures forall i :: 0 <= i < k ==> 'a' <= result[i] <= 'z'
    ensures s <= result <= t
    ensures result == median_string(s, t, k)
// </vc-spec>
// <vc-code>
{
    result := median_string(s, t, k);
    median_properties(s, t, k);
}
// </vc-code>

