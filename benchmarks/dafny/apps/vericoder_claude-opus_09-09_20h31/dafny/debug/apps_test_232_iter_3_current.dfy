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
        assert s[..i] + s[i..j] == s[..j];
        count_occurrences_concat(s[..i], s[i..j], value);
    }
}

lemma count_occurrences_concat(s1: seq<nat>, s2: seq<nat>, value: nat)
    ensures count_occurrences(s1 + s2, value) == count_occurrences(s1, value) + count_occurrences(s2, value)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        count_occurrences_concat(s1[1..], s2, value);
    }
}

lemma count_occurrences_extend(s: seq<nat>, value: nat, x: nat)
    ensures count_occurrences(s + [x], value) == count_occurrences(s, value) + if x == value then 1 else 0
{
    count_occurrences_append(s, value, x);
}

lemma empty_seq_count_zero(value: nat)
    ensures count_occurrences([], value) == 0
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
    // Check if desired is all zeros (empty subarray case)
    if sum_seq(desired) == 0 {
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
            // Empty subarray matches all-zero desired
            if n > 0 {
                assert 0 <= 0 <= 0 < n;
                assert colors[0..0+1] == colors[0..1];
                assert |colors[0..1]| == 1;
                
                // Check if first element alone satisfies
                var first_matches := true;
                k := 0;
                while k < m
                    invariant 0 <= k <= m
                    invariant first_matches <==> forall idx :: 0 <= idx < k ==> 
                             (if colors[0] == idx + 1 then 1 else 0) == desired[idx]
                {
                    var color_count := if colors[0] == k + 1 then 1 else 0;
                    if color_count != desired[k] {
                        first_matches := false;
                    }
                    k := k + 1;
                }
                
                if first_matches {
                    assert subarray_matches_desired(colors[0..1], desired, m);
                    return "YES";
                }
            }
            // If we cannot find a matching subarray, fall through to main algorithm
        }
    }
    
    if n == 0 {
        return "NO";
    }
    
    // Try all subarrays
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall ii, jj :: 0 <= ii < i && ii <= jj < n ==> !subarray_matches_desired(colors[ii..jj+1], desired, m)
    {
        var j := i;
        var current_counts := seq(m, _ => 0);
        
        while j < n
            invariant i <= j <= n
            invariant |current_counts| == m
            invariant forall color :: 1 <= color <= m ==> 
                     current_counts[color-1] == count_occurrences(colors[i..j], color)
            invariant forall jj :: i <= jj < j ==> !subarray_matches_desired(colors[i..jj+1], desired, m)
        {
            // Add colors[j] to current window
            var color := colors[j];
            var old_counts := current_counts;
            current_counts := current_counts[color-1 := current_counts[color-1] + 1];
            
            // Prove invariant maintenance
            assert colors[i..j+1] == colors[i..j] + [colors[j]];
            forall c | 1 <= c <= m
                ensures current_counts[c-1] == count_occurrences(colors[i..j+1], c)
            {
                if c == color {
                    count_occurrences_extend(colors[i..j], c, colors[j]);
                    assert current_counts[c-1] == old_counts[c-1] + 1;
                    assert current_counts[c-1] == count_occurrences(colors[i..j], c) + 1;
                    assert current_counts[c-1] == count_occurrences(colors[i..j+1], c);
                } else {
                    count_occurrences_extend(colors[i..j], c, colors[j]);
                    assert current_counts[c-1] == old_counts[c-1];
                    assert current_counts[c-1] == count_occurrences(colors[i..j], c);
                    assert current_counts[c-1] == count_occurrences(colors[i..j+1], c);
                }
            }
            
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
                assert forall idx :: 0 <= idx < m ==> current_counts[idx] == desired[idx];
                assert forall color :: 1 <= color <= m ==> current_counts[color-1] == desired[color-1];
                assert forall color :: 1 <= color <= m ==> count_occurrences(colors[i..j+1], color) == desired[color-1];
                assert subarray_matches_desired(colors[i..j+1], desired, m);
                assert 0 <= i <= j < n;
                return "YES";
            }
            
            j := j + 1;
        }
        
        i := i + 1;
    }
    
    // Assert postcondition for NO case
    assert forall ii, jj :: 0 <= ii <= jj < n ==> !subarray_matches_desired(colors[ii..jj+1], desired, m);
    return "NO";
}
// </vc-code>

