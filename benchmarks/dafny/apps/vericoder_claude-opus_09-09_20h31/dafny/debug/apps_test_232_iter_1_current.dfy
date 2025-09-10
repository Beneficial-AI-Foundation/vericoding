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
lemma count_occurrences_append(s: seq<nat>, value: nat, x: nat)
    ensures count_occurrences(s + [x], value) == 
            count_occurrences(s, value) + (if x == value then 1 else 0)
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
    }
}

lemma count_occurrences_split(s: seq<nat>, value: nat, i: nat, j: nat)
    requires 0 <= i <= j <= |s|
    ensures count_occurrences(s[i..j], value) == 
            count_occurrences(s[..j], value) - count_occurrences(s[..i], value)
{
    if i == 0 {
        assert s[..i] == [];
        assert s[i..j] == s[..j];
    } else if i == j {
        assert s[i..j] == [];
    } else {
        assert s[..j] == s[..i] + s[i..j];
        var k := i;
        while k < j
            invariant i <= k <= j
            invariant count_occurrences(s[..k], value) + count_occurrences(s[k..j], value) == count_occurrences(s[..j], value)
        {
            assert s[..k+1] == s[..k] + [s[k]];
            assert s[k..j] == [s[k]] + s[k+1..j];
            count_occurrences_append(s[..k], value, s[k]);
            k := k + 1;
        }
    }
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
    var i := 0;
    var j := 0;
    var current_counts := seq(m, _ => 0);
    
    // Initialize with empty subarray
    if sum_seq(desired) == 0 {
        // Check if desired is all zeros
        var all_zero := true;
        var k := 0;
        while k < m
            invariant 0 <= k <= m
            invariant all_zero <==> forall idx :: 0 <= idx < k ==> desired[idx] == 0
        {
            if desired[k] != 0 {
                all_zero := false;
            }
            k := k + 1;
        }
        
        if all_zero {
            return "YES";
        }
    }
    
    if n == 0 {
        return "NO";
    }
    
    // Try all subarrays
    i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        j := i;
        current_counts := seq(m, _ => 0);
        
        while j < n
            invariant i <= j <= n
            invariant |current_counts| == m
            invariant forall color :: 1 <= color <= m ==> 
                     current_counts[color-1] == count_occurrences(colors[i..j], color)
        {
            // Add colors[j] to current window
            var color := colors[j];
            current_counts := current_counts[color-1 := current_counts[color-1] + 1];
            
            // Check if current window matches desired
            var matches := true;
            var k := 0;
            while k < m
                invariant 0 <= k <= m
                invariant matches <==> forall idx :: 0 <= idx < k ==> current_counts[idx] == desired[idx]
            {
                if current_counts[k] != desired[k] {
                    matches := false;
                }
                k := k + 1;
            }
            
            if matches {
                assert subarray_matches_desired(colors[i..j+1], desired, m);
                return "YES";
            }
            
            j := j + 1;
        }
        
        i := i + 1;
    }
    
    return "NO";
}
// </vc-code>

