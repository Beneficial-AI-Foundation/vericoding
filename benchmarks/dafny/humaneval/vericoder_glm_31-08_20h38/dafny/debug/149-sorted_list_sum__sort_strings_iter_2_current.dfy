function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}

// <vc-helpers>
predicate sorted_strings(arr: seq<string>) {
  forall i, j :: 0 <= i < j < |arr| ==> comparison(arr[i], arr[j], 0)
}

lemma lemma_comparison_transitive(a: string, b: string, c: string)
    requires comparison(a, b, 0)
    requires comparison(b, c, 0)
    ensures comparison(a, c, 0)
{
    if a == b {
    } else if b == c {
    } else if a == c {
    } else {
        assert a != b && b != c && a != c;
        calc {
            comparison(a, b, 0);
        ==  { assert |a| > 0; }
            comparison(a, b, 0);
        ==  { assert a[0] == b[0]; }
            comparison(a, b, 1);
        ==  { assert comparison(a,c,0); }
            comparison(a, c, 0);
        }
    }
}

lemma lemma_comparison_antisymmetric(a: string, b: string)
    requires comparison(a, b, 0)
    requires comparison(b, a, 0)
    ensures a == b
{
    if a == b {
    } else {
        assert comparison(a,b,0);
        assert comparison(b,a,0);
        calc {
            comparison(a, b, 0);
        ==>  // Not equal
            a != b && comparison(a,b,0);
        ==  { assert a[0] == b[0]; }
            a != b && comparison(a,b,1);
        ==  { assert comparison(b,a,0) && a[0]==b[0]; }
            a != b && comparison(a,b,1) && comparison(b,a,1);
        }
        calc {
            comparison(a, b, 0);
        ==>  // Not equal
            a != b && comparison(a,b,0);
        ==>  // Not equal and first char equal
            a != b && a[0] == b[0] && comparison(a,b,1);
        }
        lemma_comparison_transitive(a,b,a);
        assert comparison(a,a,0);
        assert a == b;
    }
}

function strings_lex_order(a: string, b: string): bool {
    comparison(a, b, 0)
}

lemma lemma_strings_lex_order_is_total_order(a: string, b: string)
    ensures strings_lex_order(a, b) || strings_lex_order(b, a)
{
    if comparison(a, b, 0) {
    } else {
        assert a != b;
        calc {
            |a| <= |b|;
        }
        calc {
            !comparison(a,b,0);
        ==>  // Definition of comparison for a!=b
            !(if |a| <= |b| then true else false) || // Suffixes part
            (exists k: int :: 0 <= k < |a| && 0 <= k < |b| && a[..k] == b[..k] && a[k] > b[k]);
        }
        if |a| > |b| {
            assert strings_lex_order(b,a);
        } else {
            assert exists k: int :: 0 <= k < |a| && 0 <= k < |b| && a[..k] == b[..k] && a[k] > b[k];
            var k :| 0 <= k < |a| && 0 <= k < |b| && a[..k] == b[..k] && a[k] > b[k];
            assert a[k] > b[k];
            calc {
                comparison(b, a, 0);
            ==  // Compare first character at k
                if b[k] < a[k] then true
                else if b[k] > a[k] then false
                else comparison(b,a,k+1);
            ==  // Since a[k] > b[k] means b[k] < a[k]
                true;
            }
            assert strings_lex_order(b,a);
        }
    }
}

function strings_length_order(a: string, b: string): bool {
    |a| <= |b|
}

lemma lemma_strings_length_order_is_total_preorder(a: string, b: string)
    ensures strings_length_order(a, b) || strings_length_order(b, a)
{
    assert |a| <= |b| || |b| <= |a|;
}
// </vc-helpers>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
// </vc-spec>
// <vc-code>
if (|list| <= 1) {
    sorted := list;
} else {
    var pivot_idx := 0;
    var pivot := list[pivot_idx];
    var less, equal, greater : seq<string> := [], [], [];
    
    for i := 0 to |list|
        invariant multiset(less + equal + greater) == multiset(list)
        invariant forall j :: 0 <= j < |less| ==> strings_lex_order(less[j], pivot)
        invariant forall j :: 0 <= j < |greater| ==> strings_lex_order(pivot, greater[j])
        invariant |less| + |equal| + |greater| == i
    {
        if i == pivot_idx {
            equal := equal + [list[i]];
        } else if strings_lex_order(list[i], pivot) {
            less := less + [list[i]];
        } else {
            greater := greater + [list[i]];
        }
    }
    
    var sorted_less := sort_strings(less);
    var sorted_greater := sort_strings(greater);
    
    assert |sorted_less| == |less|;
    assert |sorted_greater| == |greater|;
    assert multiset(sorted_less) == multiset(less);
    assert multiset(sorted_greater) == multiset(greater);
    assert multiset(sorted_less) + multiset(equal) + multiset(sorted_greater) == multiset(list);
    
    sorted := sorted_less + equal + sorted_greater;
    
    forall i, j | 0 <= i < j < |sorted_less|
        ensures strings_lex_order(sorted[i], sorted[j])
    {
    }
    
    forall i | 0 <= i < |sorted_less|
        ensures strings_lex_order(sorted[i], pivot)
    {
    }

    forall j | 0 <= j < |sorted_greater|
        ensures strings_lex_order(pivot, sorted[j])
    {
    }

    forall i, j | 0 <= i < |sorted_less| && 0 <= j < |sorted_greater|
        ensures strings_lex_order(sorted[i], sorted[j])
    {
        lemma_comparison_transitive(sorted[i], pivot, sorted[j]);
    }

    forall i, j | 0 <= i < |sorted_less| && 0 <= j < |equal|
        ensures strings_lex_order(sorted[i], equal[j])
    {
        assert strings_lex_order(sorted[i], pivot);
        assert equal[j] == pivot;
    }

    forall i, j | 0 <= i < |equal| && 0 <= j < |sorted_greater|
        ensures strings_lex_order(equal[i], sorted[j])
    {
        assert equal[i] == pivot;
        assert strings_lex_order(pivot, sorted[j]);
    }
}
// </vc-code>

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
  assume{:axiom} false;
}
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}