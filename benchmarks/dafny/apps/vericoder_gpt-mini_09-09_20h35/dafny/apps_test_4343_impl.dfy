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
lemma DivQuot(a: nat, r: nat, P: nat)
    requires P > 0
    requires r < P
    ensures (a * P + r) / P == a
{
    assert a * P <= a * P + r;
    assert a * P + r < a * P + P;
    assert a * P + P == (a + 1) * P;
    assert a * P <= a * P + r < (a + 1) * P;
    assert (a * P + r) / P == a;
}

lemma StringToBase26_Bound(s: string, k: int)
    requires k >= 1
    requires |s| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    ensures string_to_base26(s) < pow26(k)
{
    if k == 1 {
        var v := (s[0] as int - 'a' as int);
        assert 0 <= v <= 25;
        assert string_to_base26(s) == v;
        assert v < pow26(1);
    } else {
        var x := (s[0] as int - 'a' as int);
        assert 0 <= x <= 25;
        StringToBase26_Bound(s[1..], k - 1);
        var rest := string_to_base26(s[1..]);
        assert rest < pow26(k - 1);
        assert string_to_base26(s) == x * pow26(k - 1) + rest;
        assert x * pow26(k - 1) + rest < 26 * pow26(k - 1);
        assert 26 * pow26(k - 1) == pow26(k);
    }
}

lemma StringToBase26_ConcatLast(p: string, c: char)
    requires forall i :: 0 <= i < |p| ==> 'a' <= p[i] <= 'z'
    requires 'a' <= c <= 'z'
    ensures string_to_base26(p + [c]) == 26 * string_to_base26(p) + (c as int - 'a' as int)
{
    if |p| == 0 {
        assert string_to_base26([c]) == (c as int - 'a' as int);
        assert 26 * string_to_base26("") + (c as int - 'a' as int) == (c as int - 'a' as int);
    } else {
        StringToBase26_ConcatLast(p[1..], c);
        var p0 := (p[0] as int - 'a' as int);
        assert 0 <= p0 <= 25;
        // unfold string_to_base26 on p + [c]
        assert string_to_base26(p + [c]) == ((p + [c])[0] as int - 'a' as int) * pow26(|p + [c]| - 1) + string_to_base26((p + [c])[1..]);
        assert (p + [c])[0] == p[0];
        assert |p + [c]| == |p| + 1;
        assert pow26(|p + [c]| - 1) == pow26(|p|);
        assert (p + [c])[1..] == p[1..] + [c];
        assert string_to_base26(p + [c]) == p0 * pow26(|p|) + string_to_base26(p[1..] + [c]);
        var cVal := (c as int - 'a' as int);
        assert string_to_base26(p[1..] + [c]) == 26 * string_to_base26(p[1..]) + cVal;
        assert p0 * pow26(|p|) + (26 * string_to_base26(p[1..]) + cVal)
               == 26 * (p0 * pow26(|p| - 1) + string_to_base26(p[1..])) + cVal;
        assert p0 * pow26(|p| - 1) + string_to_base26(p[1..]) == string_to_base26(p);
        assert string_to_base26(p + [c]) == 26 * string_to_base26(p) + cVal;
    }
}

lemma Base26ToString_ToNum(v: nat, k: int)
    requires k >= 1
    requires v < pow26(k)
    ensures string_to_base26(base26_to_string(v, k)) == v
{
    if k == 1 {
        assert base26_to_string(v, 1) == [(((v % 26) + ('a' as int)) as char)];
        assert string_to_base26(base26_to_string(v, 1)) == (v % 26);
        assert v % 26 == v;
        assert string_to_base26(base26_to_string(v, 1)) == v;
    } else {
        var prefix := base26_to_string(v / 26, k - 1);
        var lastChar := ((v % 26) + ('a' as int)) as char;
        assert v < pow26(k);
        assert v / 26 < pow26(k - 1);
        Base26ToString_ToNum(v / 26, k - 1);
        assert base26_to_string(v, k) == prefix + [lastChar];
        StringToBase26_ConcatLast(prefix, lastChar);
        var cVal := (lastChar as int - 'a' as int);
        assert string_to_base26(prefix + [lastChar]) == 26 * string_to_base26(prefix) + cVal;
        assert string_to_base26(prefix) == v / 26;
        assert 26 * (v / 26) + (v % 26) == v;
        assert string_to_base26(base26_to_string(v, k)) == v;
    }
}

lemma StringToBase26_Inj(a: string, b: string, k: int)
    requires k >= 1
    requires |a| == k && |b| == k
    requires forall i :: 0 <= i < k ==> 'a' <= a[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= b[i] <= 'z'
    requires string_to_base26(a) == string_to_base26(b)
    ensures a == b
{
    if k == 1 {
        var va := (a[0] as int - 'a' as int);
        var vb := (b[0] as int - 'a' as int);
        assert string_to_base26(a) == va;
        assert string_to_base26(b) == vb;
        assert va == vb;
        assert a[0] == b[0];
    } else {
        var a0 := (a[0] as int - 'a' as int);
        var b0 := (b[0] as int - 'a' as int);
        var ra := string_to_base26(a[1..]);
        var rb := string_to_base26(b[1..]);
        StringToBase26_Bound(a[1..], k - 1);
        StringToBase26_Bound(b[1..], k - 1);
        var P := pow26(k - 1);
        assert ra < P && rb < P;
        assert string_to_base26(a) == a0 * P + ra;
        assert string_to_base26(b) == b0 * P + rb;
        assert string_to_base26(a) == string_to_base26(b);
        assert 0 <= a0 <= 25 && 0 <= b0 <= 25;
        var a0n := (a0 as nat);
        var b0n := (b0 as nat);
        DivQuot(a0n, ra, P);
        DivQuot(b0n, rb, P);
        assert (string_to_base26(a) / P) == a0n;
        assert (string_to_base26(b) / P) == b0n;
        assert a0n == b0n;
        assert a0 == b0;
        assert ra == rb;
        StringToBase26_Inj(a[1..], b[1..], k - 1);
        assert a[1..] == b[1..];
        assert a == b;
    }
}

lemma StringToBase26_Preserves_Order(s: string, t: string, k: int)
    requires k >= 1
    requires |s| == k && |t| == k
    requires forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    requires forall i :: 0 <= i < k ==> 'a' <= t[i] <= 'z'
    requires s < t
    ensures string_to_base26(s) < string_to_base26(t)
{
    if k == 1 {
        var sv := (s[0] as int - 'a' as int);
        var tv := (t[0] as int - 'a' as int);
        assert string_to_base26(s) == sv;
        assert string_to_base26(t) == tv;
        assert sv < tv;
    } else {
        if s[0] < t[0] {
            var sa := (s[0] as int - 'a' as int);
            var ta := (t[0] as int - 'a' as int);
            assert 0 <= sa <= 25 && 0 <= ta <= 25;
            StringToBase26_Bound(s[1..], k - 1);
            StringToBase26_Bound(t[1..], k - 1);
            var rs := string_to_base26(s[1..]);
            var rt := string_to_base26(t[1..]);
            assert rs < pow26(k - 1) && rt < pow26(k - 1);
            assert string_to_base26(s) == sa * pow26(k - 1) + rs;
            assert string_to_base26(t) == ta * pow26(k - 1) + rt;
            assert sa * pow26(k - 1) + rs < ta * pow26(k - 1) + rt;
        } else if s[0] == t[0] {
            StringToBase26_Preserves_Order(s[1..], t[1..], k - 1);
            var rs := string_to_base26(s[1..]);
            var rt := string_to_base26(t[1..]);
            var firstVal := (s[0] as int - 'a' as int);
            assert string_to_base26(s) == firstVal * pow26(k - 1) + rs;
            assert string_to_base26(t) == firstVal * pow26(k - 1) + rt;
            assert rs < rt;
            assert firstVal * pow26(k - 1) + rs < firstVal * pow26(k - 1) + rt;
        } else {
            assert false;
        }
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
    var s_val := string_to_base26(s);
    var t_val := string_to_base26(t);
    StringToBase26_Bound(s, k);
    StringToBase26_Bound(t, k);
    StringToBase26_Preserves_Order(s, t, k);
    var median_val := (s_val + t_val) / 2;
    assert 2 * s_val <= s_val + t_val;
    assert s_val <= median_val;
    assert s_val + t_val <= 2 * t_val;
    assert median_val <= t_val;
    result := base26_to_string(median_val, k);
    Base26ToString_ToNum(median_val, k);
    assert string_to_base26(result) == median_val;
    assert |result| == k;
    assert forall i :: 0 <= i < k ==> 'a' <= result[i] <= 'z';
    if !(s <= result) {
        StringToBase26_Preserves_Order(result, s, k);
        assert string_to_base26(result) < string_to_base26(s);
        assert median_val < s_val;
        assert s_val <= median_val;
        assert false;
    }
    if !(result <= t) {
        StringToBase26_Preserves_Order(t, result, k);
        assert string_to_base26(t) < string_to_base26(result);
        assert t_val < median_val;
        assert median_val <= t_val;
        assert false;
    }
    assert result == median_string(s, t, k);
}
// </vc-code>

