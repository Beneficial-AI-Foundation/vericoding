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
lemma string_to_base26_monotonic(s: string, t: string)
    requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < |t| ==> 'a' <= t[i] <= 'z'
    requires |s| == |t|
    requires s < t
    ensures string_to_base26(s) < string_to_base26(t)
{
    if |s| == 0 {
        return;
    }
    if s[0] < t[0] {
        return;
    }
    if s[0] == t[0] {
        string_to_base26_monotonic(s[1..], t[1..]);
    }
}

lemma pow26_positive(k: int)
    requires k >= 0
    ensures pow26(k) > 0
{
}

lemma base26_string_inverse(val: nat, k: int)
    requires k >= 1
    ensures string_to_base26(base26_to_string(val, k)) == val % pow26(k)
{
    pow26_positive(k);
    if k == 1 {
        return;
    }
    base26_string_inverse(val / 26, k - 1);
    pow26_positive(k - 1);
}

lemma string_base26_inverse(s: string)
    requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
    requires |s| >= 1
    ensures base26_to_string(string_to_base26(s), |s|) == s
{
    if |s| == 1 {
        return;
    }
    string_base26_inverse(s[1..]);
    pow26_positive(|s| - 1);
}

lemma median_bounds(s: string, t: string, k: int)
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    ensures s <= median_string(s, t, k) <= t
{
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    string_to_base26_monotonic(s, t);
    assert s_val < t_val;
    var median_val := (s_val + t_val) / 2;
    assert s_val <= median_val <= t_val;
    
    string_base26_inverse(s);
    string_base26_inverse(t);
    
    if median_val == s_val {
        assert median_string(s, t, k) == s;
    } else if median_val == t_val {
        assert median_string(s, t, k) == t;
    } else {
        assert s_val < median_val < t_val;
    }
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
    median_bounds(s, t, k);
}
// </vc-code>

