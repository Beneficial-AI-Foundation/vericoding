function count_occurrences(s: seq<nat>, value: nat): nat
{
    if |s| == 0 then 0
    else if s[0] == value then 1 + count_occurrences(s[1..], value)
    else count_occurrences(s[1..], value)
}

function sum_seq(s: seq<nat>): nat
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

predicate subarray_matches_desired(subarray: seq<nat>, desired: seq<nat>, m: nat)
    requires |desired| == m
{
    forall color :: 1 <= color <= m ==> count_occurrences(subarray, color) == desired[color-1]
}

predicate ValidInput(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>)
{
    |colors| == n &&
    |desired| == m &&
    (forall i :: 0 <= i < |colors| ==> 1 <= colors[i] <= m) &&
    (forall i :: 0 <= i < |desired| ==> desired[i] >= 0) &&
    sum_seq(desired) <= n
}

// <vc-helpers>
lemma count_occurrences_slice(s: seq<nat>, value: nat, start: nat, end: nat)
  requires 0 <= start <= end <= |s|
  ensures count_occurrences(s[start..end], value) == count_occurrences(s, value) - count_occurrences(s[0..start], value) - count_occurrences(s[end..], value)
{
}

lemma count_occurrences_append(s1: seq<nat>, s2: seq<nat>, value: nat)
  ensures count_occurrences(s1 + s2, value) == count_occurrences(s1, value) + count_occurrences(s2, value)
{
}

lemma subarray_matches_desired_implies(s: seq<nat>, desired: seq<nat>, m: nat, i: nat, j: nat)
  requires |desired| == m
  requires 0 <= i <= j < |s|
  requires subarray_matches_desired(s[i..j+1], desired, m)
  ensures exists i', j' :: 0 <= i' <= j' < |s| && subarray_matches_desired(s[i'..j'+1], desired, m)
{
}

lemma sliding_window_lemma(colors: seq<nat>, desired: seq<nat>, m: nat, left: nat, right: nat, counts: seq<nat>)
  requires |desired| == m
  requires |counts| == m
  requires 0 <= left <= right <= |colors|
  requires forall color :: 1 <= color <= m ==> counts[color-1] == count_occurrences(colors[left..right], color)
  ensures (subarray_matches_desired(colors[left..right], desired, m) <==> forall color :: 1 <= color <= m ==> counts[color-1] == desired[color-1])
{
}

lemma sum_seq_lemma(s: seq<nat>)
  ensures sum_seq(s) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>) returns (result: string)
    requires ValidInput(n, m, colors, desired)
    ensures result == "YES" <==> exists i, j :: 0 <= i <= j < n && subarray_matches_desired(colors[i..j+1], desired, m)
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
    var total_needed := sum_seq(desired);
    if total_needed == 0 {
        result := "YES";
        return;
    }
    if total_needed > n {
        result := "NO";
        return;
    }
    
    var left := 0;
    var right := 0;
    var counts : seq<nat> := [];
    var i := 0;
    while i < m 
        invariant |counts| == i
    {
        counts := counts + [0];
        i := i + 1;
    }
    
    var match: bool;
    var c: nat;
    
    while right < n {
        var color := colors[right];
        counts := counts[..color-1] + [counts[color-1] + 1] + counts[color..];
        right := right + 1;
        
        while sum_seq(counts) > total_needed && left < right {
            color := colors[left];
            counts := counts[..color-1] + [counts[color-1] - 1] + counts[color..];
            left := left + 1;
        }
        
        if sum_seq(counts) == total_needed {
            match := true;
            c := 1;
            while c <= m 
                invariant match ==> (forall k :: 1 <= k < c ==> counts[k-1] == desired[k-1])
            {
                if counts[c-1] != desired[c-1] {
                    match := false;
                }
                c := c + 1;
            }
            if match {
                result := "YES";
                return;
            }
        }
    }
    
    result := "NO";
}
// </vc-code>

