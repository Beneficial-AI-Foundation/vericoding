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
lemma Base26ToString_Roundtrip_String(s: string, k: int)
    requires k >= 1
    requires |s| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    ensures base26_to_string(string_to_base26(s), k) == s
{
    var v := string_to_base26(s);
    StringToBase26_Bound(s, k);
    assert v < pow26(k);
    Base26ToString_ToNum(v, k);
    // string_to_base26(base26_to_string(v,k)) == v
    StringToBase26_Inj(base26_to_string(v, k), s, k);
    // hence base26_to_string(v,k) == s
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
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    StringToBase26_Bound(s, k);
    StringToBase26_Bound(t, k);
    StringToBase26_Preserves_Order(s, t, k);
    var median_val := (s_val + t_val) / 2;
    // Prove s_val <= median_val <= t_val
    assert 2 * s_val <= s_val + t_val;
    assert s_val <= median_val;
    assert s_val + t_val <= 2 * t_val;
    assert median_val <= t_val;
    result := base26_to_string(median_val, k);
    Base26ToString_ToNum(median_val, k);
    assert string_to_base26(result) == median_val;
    assert |result| == k;
    assert forall i :: 0 <= i < k ==> 'a' <= result[i] <= 'z';
    // Prove s <= result
    if !(s <= result) {
        // result < s leads to numeric contradiction
        StringToBase26_Preserves_Order(result, s, k);
        assert string_to_base26(result) < string_to_base26(s);
        assert median_val < s_val;
        assert s_val <= median_val;
        assert false;
    }
    // Prove result <= t
    if !(result <= t) {
        // t < result leads to numeric contradiction
        StringToBase26_Preserves_Order(t, result, k);
        assert string_to_base26(t) < string_to_base26(result);
        assert t_val < median_val;
        assert median_val <= t_val;
        assert false;
    }
    // Finally, result equals the median_string by definition
    assert result == median_string(s, t, k);
}
// </vc-code>

