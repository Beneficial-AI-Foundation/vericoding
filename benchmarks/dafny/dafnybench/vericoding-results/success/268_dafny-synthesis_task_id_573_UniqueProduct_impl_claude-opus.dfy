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
    calc {
        SetProduct({x});
        == { assert x in {x}; }
        x * SetProduct({x} - {x});
        == 
        x * SetProduct({});
        ==
        x * 1;
        ==
        x;
    }
}

lemma SetProductChoice(s: set<int>, x: int)
    requires x in s
    ensures SetProduct(s) == x * SetProduct(s - {x})
    decreases s
{
    if s == {x} {
        SetProductSingleton(x);
    } else {
        var y :| y in s && SetProduct(s) == y * SetProduct(s - {y});
        if y == x {
            // The choice is already x, so we're done
        } else {
            // y != x, both are in s
            assert x in s - {y};
            assert y in s - {x};
            
            // We need to show that SetProduct(s - {y}) == x * SetProduct((s - {y}) - {x})
            SetProductChoice(s - {y}, x);
            
            // And that SetProduct(s - {x}) == y * SetProduct((s - {x}) - {y})
            SetProductChoice(s - {x}, y);
            
            // Now we can show the equality
            assert (s - {y}) - {x} == (s - {x}) - {y};
            assert SetProduct(s) == y * SetProduct(s - {y});
            assert SetProduct(s - {y}) == x * SetProduct((s - {y}) - {x});
            assert SetProduct(s) == y * x * SetProduct((s - {y}) - {x});
            assert SetProduct(s) == x * y * SetProduct((s - {x}) - {y});
            assert SetProduct(s - {x}) == y * SetProduct((s - {x}) - {y});
            assert SetProduct(s) == x * SetProduct(s - {x});
        }
    }
}

lemma SetProductUnion(s1: set<int>, s2: set<int>)
    requires s1 !! s2  // disjoint sets
    ensures SetProduct(s1 + s2) == SetProduct(s1) * SetProduct(s2)
{
    if s1 == {} {
        calc {
            SetProduct(s1 + s2);
            ==
            SetProduct({} + s2);
            == { assert {} + s2 == s2; }
            SetProduct(s2);
            == { SetProductEmpty(); }
            1 * SetProduct(s2);
            == { SetProductEmpty(); }
            SetProduct({}) * SetProduct(s2);
            ==
            SetProduct(s1) * SetProduct(s2);
        }
    } else {
        var x :| x in s1;
        calc {
            SetProduct(s1 + s2);
            == { assert x in s1 + s2; 
                 SetProductChoice(s1 + s2, x); }
            x * SetProduct((s1 + s2) - {x});
            == { assert x !in s2 by { assert s1 !! s2; }
                 assert (s1 + s2) - {x} == (s1 - {x}) + s2; }
            x * SetProduct((s1 - {x}) + s2);
            == { assert (s1 - {x}) !! s2 by { assert s1 !! s2; }
                 SetProductUnion(s1 - {x}, s2); }
            x * (SetProduct(s1 - {x}) * SetProduct(s2));
            ==
            (x * SetProduct(s1 - {x})) * SetProduct(s2);
            == { assert x in s1; 
                 SetProductChoice(s1, x); }
            SetProduct(s1) * SetProduct(s2);
        }
    }
}

lemma SetProductAdd(s: set<int>, x: int)
    requires x !in s
    ensures SetProduct(s + {x}) == SetProduct(s) * x
{
    SetProductUnion(s, {x});
    SetProductSingleton(x);
}
// </vc-helpers>

// <vc-spec>
method UniqueProduct (arr: array<int>) returns (product: int)
   ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
// </vc-spec>
// <vc-code>
{
    product := 1;
    var seen: set<int> := {};
    var i := 0;

    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant seen == set j | 0 <= j < i :: arr[j]
        invariant product == SetProduct(seen)
    {
        if arr[i] !in seen {
            SetProductAdd(seen, arr[i]);
            product := product * arr[i];
            seen := seen + {arr[i]};
        }
        i := i + 1;
    }
}
// </vc-code>

