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
lemma StringToBase26_Bound(s: string, k: int)
    requires k >= 1
    requires |s| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    ensures string_to_base26(s) < pow26(k)
{
    if k == 1 {
        // string_to_base26(s) == s[0]-'a' < 26 == pow26(1)
        assert string_to_base26(s) == (s[0] as int - 'a' as int);
        assert (s[0] as int - 'a' as int) < 26;
        assert pow26(1) == 26;
    } else {
        var head := (s[0] as int - 'a' as int);
        var tail := s[1..];
        StringToBase26_Bound(tail, k - 1);
        assert string_to_base26(s) == head * pow26(k - 1) + string_to_base26(tail);
        assert head < 26;
        assert string_to_base26(tail) < pow26(k - 1);
        assert head * pow26(k - 1) + string_to_base26(tail) < 26 * pow26(k - 1);
        assert 26 * pow26(k - 1) == pow26(k);
    }
}

lemma StringToBase26_Preserves_Order(s: string, t: string, k: int)
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    ensures string_to_base26(s) < string_to_base26(t)
    decreases k
{
    if k == 1 {
        assert s[0] < t[0];
        assert (s[0] as int - 'a' as int) < (t[0] as int - 'a' as int);
        assert string_to_base26(s) == (s[0] as int - 'a' as int);
        assert string_to_base26(t) == (t[0] as int - 'a' as int);
    } else {
        if s[0] < t[0] {
            var s0 := (s[0] as int - 'a' as int);
            var t0 := (t[0] as int - 'a' as int);
            var ss := s[1..];
            var tt := t[1..];
            assert string_to_base26(s) == s0 * pow26(k - 1) + string_to_base26(ss);
            assert string_to_base26(t) == t0 * pow26(k - 1) + string_to_base26(tt);
            assert s0 < t0;
            // since pow26(k-1) >= 1 and t0 - s0 >= 1, the difference is positive
        } else {
            // s[0] == t[0]
            var ss := s[1..];
            var tt := t[1..];
            // s < t and equal heads implies ss < tt
            assert ss < tt;
            StringToBase26_Preserves_Order(ss, tt, k - 1);
            var s0 := (s[0] as int - 'a' as int);
            assert string_to_base26(s) == s0 * pow26(k - 1) + string_to_base26(ss);
            assert string_to_base26(t) == s0 * pow26(k - 1) + string_to_base26(tt);
        }
    }
}

lemma Base26ToString_ToNum(v: nat, k: int)
    requires k >= 1
    requires v < pow26(k)
    ensures string_to_base26(base26_to_string(v, k)) == v
    decreases k
{
    if k == 1 {
        // base26_to_string(v,1) == [((v % 26) + 'a') as char]
        // string_to_base26 of that equals ( (v % 26) ) and since v < 26, v%26 == v
        assert base26_to_string(v, 1) == [((v % 26) + ('a' as int)) as char];
        assert string_to_base26(base26_to_string(v, 1)) == ((base26_to_string(v, 1)[0] as int - 'a' as int));
        assert ((base26_to_string(v, 1)[0] as int - 'a' as int) == (v % 26));
        assert v % 26 == v; // because v < 26
    } else {
        var q := v / 26;
        var d := v % 26;
        // base26_to_string(v,k) == base26_to_string(q,k-1) + [d+'a']
        assert base26_to_string(v, k) == base26_to_string(q, k - 1) + [((v % 26) + ('a' as int)) as char];
        Base26ToString_ToNum(q, k - 1);
        // string_to_base26(base26_to_string(v,k)) == string_to_base26(base26_to_string(q,k-1)) * 26 + d
        assert string_to_base26(base26_to_string(v, k)) ==
               string_to_base26(base26_to_string(q, k - 1)) * 26 + (base26_to_string(v, k)[k - 1] as int - 'a' as int);
        assert (base26_to_string(v, k)[k - 1] as int - 'a' as int) == d;
        assert string_to_base26(base26_to_string(q, k - 1)) == q;
        assert q * 26 + d == v;
    }
}

lemma StringToBase26_Inj(s: string, t: string, k: int)
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    ensures string_to_base26(s) == string_to_base26(t) ==> s == t
    decreases k
{
    if k == 1 {
        if string_to_base26(s) == string_to_base26(t) {
            assert (s[0] as int - 'a' as int) == (t[0] as int - 'a' as int);
            assert s[0] == t[0];
        }
    } else {
        if string_to_base26(s) == string_to_base26(t) {
            var s0 := (s[0] as int - 'a' as int);
            var t0 := (t[0] as int - 'a' as int);
            var ss := s[1..];
            var tt := t[1..];
            assert string_to_base26(s) == s0 * pow26(k - 1) + string_to_base26(ss);
            assert string_to_base26(t) == t0 * pow26(k - 1) + string_to_base26(tt);
            assert s0 * pow26(k - 1) + string_to_base26(ss) == t0 * pow26(k - 1) + string_to_base26(tt);
            // From equality deduce s0 == t0 and string_to_base26(ss) == string_to_base26(tt)
            assert s0 == t0;
            assert string_to_base26(ss) == string_to_base26(tt);
            StringToBase26_Inj(ss, tt, k - 1);
            assert ss == tt;
            assert s[0] == t[0];
        }
    }
}

lemma Base26ToString_Roundtrip_String(s: string, k: int)
    requires k >= 1
    requires |s| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    ensures base26_to_string(string
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
lemma StringToBase26_Bound(s: string, k: int)
    requires k >= 1
    requires |s| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    ensures string_to_base26(s) < pow26(k)
{
    if k == 1 {
        // string_to_base26(s) == s[0]-'a' < 26 == pow26(1)
        assert string_to_base26(s) == (s[0] as int - 'a' as int);
        assert (s[0] as int - 'a' as int) < 26;
        assert pow26(1) == 26;
    } else {
        var head := (s[0] as int - 'a' as int);
        var tail := s[1..];
        StringToBase26_Bound(tail, k - 1);
        assert string_to_base26(s) == head * pow26(k - 1) + string_to_base26(tail);
        assert head < 26;
        assert string_to_base26(tail) < pow26(k - 1);
        assert head * pow26(k - 1) + string_to_base26(tail) < 26 * pow26(k - 1);
        assert 26 * pow26(k - 1) == pow26(k);
    }
}

lemma StringToBase26_Preserves_Order(s: string, t: string, k: int)
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    ensures string_to_base26(s) < string_to_base26(t)
    decreases k
{
    if k == 1 {
        assert s[0] < t[0];
        assert (s[0] as int - 'a' as int) < (t[0] as int - 'a' as int);
        assert string_to_base26(s) == (s[0] as int - 'a' as int);
        assert string_to_base26(t) == (t[0] as int - 'a' as int);
    } else {
        if s[0] < t[0] {
            var s0 := (s[0] as int - 'a' as int);
            var t0 := (t[0] as int - 'a' as int);
            var ss := s[1..];
            var tt := t[1..];
            assert string_to_base26(s) == s0 * pow26(k - 1) + string_to_base26(ss);
            assert string_to_base26(t) == t0 * pow26(k - 1) + string_to_base26(tt);
            assert s0 < t0;
            // since pow26(k-1) >= 1 and t0 - s0 >= 1, the difference is positive
        } else {
            // s[0] == t[0]
            var ss := s[1..];
            var tt := t[1..];
            // s < t and equal heads implies ss < tt
            assert ss < tt;
            StringToBase26_Preserves_Order(ss, tt, k - 1);
            var s0 := (s[0] as int - 'a' as int);
            assert string_to_base26(s) == s0 * pow26(k - 1) + string_to_base26(ss);
            assert string_to_base26(t) == s0 * pow26(k - 1) + string_to_base26(tt);
        }
    }
}

lemma Base26ToString_ToNum(v: nat, k: int)
    requires k >= 1
    requires v < pow26(k)
    ensures string_to_base26(base26_to_string(v, k)) == v
    decreases k
{
    if k == 1 {
        // base26_to_string(v,1) == [((v % 26) + 'a') as char]
        // string_to_base26 of that equals ( (v % 26) ) and since v < 26, v%26 == v
        assert base26_to_string(v, 1) == [((v % 26) + ('a' as int)) as char];
        assert string_to_base26(base26_to_string(v, 1)) == ((base26_to_string(v, 1)[0] as int - 'a' as int));
        assert ((base26_to_string(v, 1)[0] as int - 'a' as int) == (v % 26));
        assert v % 26 == v; // because v < 26
    } else {
        var q := v / 26;
        var d := v % 26;
        // base26_to_string(v,k) == base26_to_string(q,k-1) + [d+'a']
        assert base26_to_string(v, k) == base26_to_string(q, k - 1) + [((v % 26) + ('a' as int)) as char];
        Base26ToString_ToNum(q, k - 1);
        // string_to_base26(base26_to_string(v,k)) == string_to_base26(base26_to_string(q,k-1)) * 26 + d
        assert string_to_base26(base26_to_string(v, k)) ==
               string_to_base26(base26_to_string(q, k - 1)) * 26 + (base26_to_string(v, k)[k - 1] as int - 'a' as int);
        assert (base26_to_string(v, k)[k - 1] as int - 'a' as int) == d;
        assert string_to_base26(base26_to_string(q, k - 1)) == q;
        assert q * 26 + d == v;
    }
}

lemma StringToBase26_Inj(s: string, t: string, k: int)
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    ensures string_to_base26(s) == string_to_base26(t) ==> s == t
    decreases k
{
    if k == 1 {
        if string_to_base26(s) == string_to_base26(t) {
            assert (s[0] as int - 'a' as int) == (t[0] as int - 'a' as int);
            assert s[0] == t[0];
        }
    } else {
        if string_to_base26(s) == string_to_base26(t) {
            var s0 := (s[0] as int - 'a' as int);
            var t0 := (t[0] as int - 'a' as int);
            var ss := s[1..];
            var tt := t[1..];
            assert string_to_base26(s) == s0 * pow26(k - 1) + string_to_base26(ss);
            assert string_to_base26(t) == t0 * pow26(k - 1) + string_to_base26(tt);
            assert s0 * pow26(k - 1) + string_to_base26(ss) == t0 * pow26(k - 1) + string_to_base26(tt);
            // From equality deduce s0 == t0 and string_to_base26(ss) == string_to_base26(tt)
            assert s0 == t0;
            assert string_to_base26(ss) == string_to_base26(tt);
            StringToBase26_Inj(ss, tt, k - 1);
            assert ss == tt;
            assert s[0] == t[0];
        }
    }
}

lemma Base26ToString_Roundtrip_String(s: string, k: int)
    requires k >= 1
    requires |s| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    ensures base26_to_string(string
// </vc-code>

