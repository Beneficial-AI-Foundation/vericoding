predicate ValidInput(diameters: seq<int>)
{
    |diameters| > 0 && forall i :: 0 <= i < |diameters| ==> diameters[i] > 0
}

function num_distinct(s: seq<int>): int
    ensures num_distinct(s) >= 0
    ensures num_distinct(s) <= |s|
    ensures |s| == 0 ==> num_distinct(s) == 0
    ensures |s| > 0 ==> num_distinct(s) >= 1
{
    if |s| == 0 then 0
    else if s[0] in s[1..] then num_distinct(s[1..])
    else 1 + num_distinct(s[1..])
}

// <vc-helpers>
lemma SeqHeadRestMembership(s: seq<int>)
    ensures |s| > 0 ==> forall y :: y in s <==> y == s[0] || y in s[1..]
{
    if |s| == 0 {
        // vacuous
    } else {
        var x := s[0];
        var rest := s[1..];
        // Prove both directions
        assert forall y :: (y in s) ==> (y == x || y in rest)
        by {
            // take arbitrary y with y in s
            assume yCond: y in s;
            // membership in sequence yields an index
            // There exists k with 0 <= k < |s| and s[k] == y
            var found := (exists k :: 0 <= k < |s| && s[k] == y);
            // We can inspect the index: if k == 0 then y == x else y in rest
            if y == x {
                // immediate
            } else {
                // y != x, but y in s, thus the index cannot be 0, so y must be in rest
                assert y in rest;
            }
        }
        assert forall y :: (y == x || y in rest) ==> (y in s)
        by {
            assume H: (y == x || y in rest);
            if y == x {
                // y equals the head -> in s
            } else {
                // y in rest implies present in s
            }
        }
    }
}

lemma DistinctCountSetLemma(s: seq<int>) 
    ensures num_distinct(s) == |set s|
    decreases |s|
{
    if |s| == 0 {
        // num_distinct([]) == 0 and |set []| == 0
        assert num_distinct(s) == 0;
        assert |set s| == 0;
    } else {
        var x := s[0];
        var rest := s[1..];
        DistinctCountSetLemma(rest);
        // Use membership decomposition for s = [x] + rest
        SeqHeadRestMembership(s);
        if x in rest {
            // show set s == set rest
            assert forall y :: y in set s ==> y in set rest
            by {
                assume yIn: y in set s;
                // by SeqHeadRestMembership, y in s implies y == x || y in rest
                if y == x {
                    // x in rest, hence y in rest
                } else {
                    // y in rest
                }
            }
            assert forall y :: y in set rest ==> y in set s
            by {
                assume yIn: y in set rest;
                // rest elements are in s
            }
            assert |set s| == |set rest|;
            assert num_distinct(s) == num_distinct(rest);
            assert num_distinct(rest) == |set rest|;
            assert num_distinct(s) == |set s|;
        } else {
            // x not in rest -> set s == set rest + {x}
            assert forall y :: y in set s ==> y in set rest || y == x
            by {
                assume yIn: y in set s;
                if y == x {
                    // OK
                } else {
                    // then y in rest
                }
            }
            assert forall y :: (y in set rest || y == x) ==> y in set s
            by {
                assume H: (y in set rest || y == x);
                if y == x {
                    // in s
                } else {
                    // y in rest -> in s
                }
            }
            // Since x not in rest, {x} is disjoint from set rest
            assert x !in set rest;
            assert |set s| == |set rest| + 1;
            assert num_distinct(s) == 1 + num_distinct(rest);
            assert num_distinct(rest) == |set rest|;
            assert num_distinct(s) == |set s|;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(diameters: seq<int>) returns (result: int)
    requires ValidInput(diameters)
    ensures result == num_distinct(diameters)
    ensures result >= 1
    ensures result <= |diameters|
// </vc-spec>
// <vc-code>
{
    var seen: set<int> := {};
    var i := 0;
    while i < |diameters|
        invariant 0 <= i <= |diameters|
        invariant seen == set diameters[..i]
    {
        if diameters[i] !in seen {
            seen := seen + { diameters[i] };
        }
        i := i + 1;
    }
    // now seen == set diameters
    DistinctCountSetLemma(diameters);
    result := |seen|;
    assert result == num_distinct(diameters);
}
// </vc-code>

