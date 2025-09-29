predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

// <vc-helpers>
lemma SetCardAddElement<T>(s: set<T>, x: T)
    ensures x in s ==> |s + {x}| == |s|
    ensures x !in s ==> |s + {x}| == |s| + 1
{
    if x in s {
        assert s + {x} == s;
    } else {
        assert s + {x} == s + {x};
        assert (s + {x}) * s == s;
        assert x !in s;
    }
}

lemma SubsetCardinality<T>(s1: set<T>, s2: set<T>)
    requires s1 <= s2
    ensures |s1| <= |s2|
{
    if s1 == s2 {
        assert |s1| == |s2|;
    } else {
        var diff := s2 - s1;
        // Since s1 != s2 and s1 <= s2, there must be an element in s2 that's not in s1
        assert s1 != s2 && s1 <= s2;
        assert exists x :: x in s2 && x !in s1;
        assert diff == (s2 - s1) != {};
        assert s2 == s1 + diff;
        assert s1 * diff == {};
        assert |s2| == |s1| + |diff|;
        assert |diff| >= 1;
        assert |s1| <= |s2|;
    }
}
// </vc-helpers>

// <vc-spec>
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// </vc-spec>
// <vc-code>
{
    var indices: set<int> := {};
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant indices == set j: int | 0 <= j < i && IsUpperCase(s[j])
    {
        if IsUpperCase(s[i]) {
            indices := indices + {i};
        }
        i := i + 1;
    }
    
    count := |indices|;
}
// </vc-code>

