predicate ValidInput(n: int, scores: seq<int>)
{
    n == |scores| && n >= 1 && exists i :: 0 <= i < |scores| && scores[i] != 0
}

function UniqueNonZeroScores(scores: seq<int>): set<int>
{
    set i | 0 <= i < |scores| && scores[i] != 0 :: scores[i]
}

predicate ValidResult(scores: seq<int>, result: int)
{
    result >= 1 && 
    result == |UniqueNonZeroScores(scores)| && 
    result <= |scores|
}

// <vc-helpers>
lemma UniqueNonZeroScoresAppend(s: seq<int>, x: int)
    ensures UniqueNonZeroScores(s + [x]) == 
        if x != 0 then UniqueNonZeroScores(s) + {x} 
        else UniqueNonZeroScores(s)
{
    if x != 0 {
        calc {
            UniqueNonZeroScores(s + [x]);
            == { def of UniqueNonZeroScores }
            set i | 0 <= i < |s|+1 && (s+[x])[i] != 0 :: (s+[x])[i];
            == { split the range: [0, |s|) and [|s|, |s|+1) }
            (set i | 0 <= i < |s| && s[i] != 0 :: s[i]) ∪ {x};
            == { def of UniqueNonZeroScores(s) }
            UniqueNonZeroScores(s) ∪ {x};
            == { since x != 0, and set union with a singleton is the same as adding the element }
            UniqueNonZeroScores(s) + {x};
        }
    } else {
        calc {
            UniqueNonZeroScores(s + [x]);
            == { def of UniqueNonZeroScores }
            set i | 0 <= i < |s|+1 && (s+[x])[i] != 0 :: (s+[x])[i];
            == { because x==0, the last element is 0 so it is excluded. Also, for i in [0,|s|): (s+[x])[i] = s[i] }
            set i | 0 <= i < |s| && s[i] != 0 :: s[i];
            == { def of UniqueNonZeroScores(s) }
            UniqueNonZeroScores(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, scores)
    ensures ValidResult(scores, result)
// </vc-spec>
// <vc-code>
{
    var uniqueSet := {};
    for i := 0 to |scores|
        invariant uniqueSet == UniqueNonZeroScores(scores[0..i])
    {
        UniqueNonZeroScoresAppend(scores[0..i], scores[i]);
        if scores[i] != 0 {
            uniqueSet := uniqueSet + {scores[i]};
        }
    }
    result := |uniqueSet|;
}
// </vc-code>

