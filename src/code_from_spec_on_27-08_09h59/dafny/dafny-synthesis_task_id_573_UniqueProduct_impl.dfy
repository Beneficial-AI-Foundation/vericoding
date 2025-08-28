ghost function SetProduct(s : set<int>) : int
{
    if s == {} then 1
    else var x :| x in s; 
         x * SetProduct(s - {x})
}

// <vc-helpers>
lemma SetProductEmpty()
    ensures SetProduct({}) == 1
{
}

lemma SetProductSingleton(x: int)
    ensures SetProduct({x}) == x
{
}

lemma SetProductChoice(s: set<int>, x: int, y: int)
    requires x in s && y in s
    ensures x * SetProduct(s - {x}) == y * SetProduct(s - {y})
{
    if x == y {
        // trivial case
    } else {
        var s1 := s - {x};
        var s2 := s - {y};
        assert y in s1 && x in s2;
        var common := s - {x} - {y};
        assert s1 - {y} == common;
        assert s2 - {x} == common;
        
        // Both sides equal y * x * SetProduct(common)
        assert x * SetProduct(s1) == x * y * SetProduct(common);
        assert y * SetProduct(s2) == y * x * SetProduct(common);
    }
}

lemma SetProductInsert(s: set<int>, x: int)
    requires x !in s
    ensures SetProduct(s + {x}) == x * SetProduct(s)
    decreases s
{
    var s_union := s + {x};
    assert x in s_union;
    
    if s == {} {
        SetProductSingleton(x);
        SetProductEmpty();
    } else {
        var y :| y in s;
        assert y in s_union && y != x;
        
        SetProductChoice(s_union, x, y);
        assert x * SetProduct(s_union - {x}) == y * SetProduct(s_union - {y});
        assert s_union - {x} == s;
        assert s_union - {y} == (s - {y}) + {x};
        assert x !in (s - {y});
        SetProductInsert(s - {y}, x);
        
        calc {
            SetProduct(s_union);
            y * SetProduct(s_union - {y});
            y * SetProduct((s - {y}) + {x});
            y * x * SetProduct(s - {y});
            x * (y * SetProduct(s - {y}));
            x * SetProduct(s);
        }
    }
}

lemma ArrayToSetProductInvariant(arr: array<int>, i: int, product: int)
    requires 0 <= i <= arr.Length
    requires product == SetProduct((set j | 0 <= j < i :: arr[j]))
    ensures product == SetProduct((set j | 0 <= j < i :: arr[j]))
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    product := 1;
    var i := 0;
    
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant product == SetProduct((set j | 0 <= j < i :: arr[j]))
    {
        var currentSet := set j | 0 <= j < i :: arr[j];
        var nextSet := set j | 0 <= j < i + 1 :: arr[j];
        
        assert nextSet == currentSet + {arr[i]};
        
        if arr[i] in currentSet {
            assert nextSet == currentSet;
            assert SetProduct(nextSet) == SetProduct(currentSet);
        } else {
            SetProductInsert(currentSet, arr[i]);
            assert SetProduct(nextSet) == arr[i] * SetProduct(currentSet);
            product := product * arr[i];
        }
        
        i := i + 1;
    }
    
    assert (set j | 0 <= j < i :: arr[j]) == (set j | 0 <= j < arr.Length :: arr[j]);
}
// </vc-code>
