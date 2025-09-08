Given two strings s and t of length k consisting of lowercase Latin letters,
where s is lexicographically less than t, find the median string in the
lexicographically ordered list of all strings of length k that are
lexicographically between s and t (inclusive).

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
{
    var aa := new int[k + 1];
    var bb := new int[k + 1];
    var cc := new int[k + 1];

    var i := 0;
    while i <= k
        invariant 0 <= i <= k + 1
    {
        aa[i] := 0;
        bb[i] := 0;
        cc[i] := 0;
        i := i + 1;
    }

    i := 0;
    while i < k
        invariant 0 <= i <= k
    {
        aa[i] := (s[k - 1 - i] as int) - ('a' as int);
        i := i + 1;
    }

    i := 0;
    while i < k
        invariant 0 <= i <= k
    {
        bb[i] := (t[k - 1 - i] as int) - ('a' as int);
        i := i + 1;
    }

    var carry := 0;
    i := 0;
    while i <= k
        invariant 0 <= i <= k + 1
    {
        cc[i] := aa[i] + bb[i] + carry;
        if cc[i] >= 26 {
            carry := 1;
            cc[i] := cc[i] - 26;
        } else {
            carry := 0;
        }
        i := i + 1;
    }

    carry := 0;
    i := k;
    while i >= 0
        invariant -1 <= i <= k
    {
        var value := carry * 26 + cc[i];
        carry := value % 2;
        cc[i] := value / 2;
        i := i - 1;
    }

    result := "";
    i := k - 1;
    while i >= 0
        invariant -1 <= i <= k - 1
    {
        var ch := (cc[i] + ('a' as int)) as char;
        result := result + [ch];
        i := i - 1;
    }
}
