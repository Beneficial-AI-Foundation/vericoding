Given N mochi with diameters, find the maximum number of layers in a kagami mochi.
A kagami mochi is a stack where each layer has a strictly smaller diameter than the layer below it.
This is equivalent to counting the number of distinct diameters in the input.

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

function filter_not_equal(s: seq<int>, val: int): seq<int>
    ensures forall x :: x in filter_not_equal(s, val) ==> x != val
    ensures forall x :: x in filter_not_equal(s, val) ==> x in s
    ensures |filter_not_equal(s, val)| <= |s|
    ensures val in s ==> |filter_not_equal(s, val)| < |s|
{
    if |s| == 0 then []
    else if s[0] != val then [s[0]] + filter_not_equal(s[1..], val)
    else filter_not_equal(s[1..], val)
}

function max_seq(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_seq(s)
    ensures max_seq(s) in s
{
    if |s| == 1 then s[0]
    else if s[0] >= max_seq(s[1..]) then s[0]
    else max_seq(s[1..])
}

lemma lemma_remove_distinct_element(s: seq<int>, val: int)
    requires val in s
    ensures num_distinct(s) == 1 + num_distinct(filter_not_equal(s, val))
{
    if |s| == 0 {
    } else if s[0] == val {
        if s[0] in s[1..] {
            lemma_remove_distinct_element(s[1..], val);
        } else {
            lemma_filter_not_equal_preserves_distinct(s[1..], val);
        }
    } else {
        lemma_remove_distinct_element(s[1..], val);
        if s[0] in s[1..] {
            lemma_filter_preserves_membership(s[1..], s[0], val);
        }
    }
}

lemma lemma_filter_not_equal_preserves_distinct(s: seq<int>, val: int)
    requires val !in s
    ensures filter_not_equal(s, val) == s
    ensures num_distinct(filter_not_equal(s, val)) == num_distinct(s)
{
    if |s| == 0 {
    } else {
        lemma_filter_not_equal_preserves_distinct(s[1..], val);
    }
}

lemma lemma_filter_preserves_membership(s: seq<int>, elem: int, val: int)
    requires elem != val
    requires elem in s
    ensures elem in filter_not_equal(s, val)
{
    if |s| > 0 {
        if s[0] == elem {
        } else {
            lemma_filter_preserves_membership(s[1..], elem, val);
        }
    }
}

method solve(diameters: seq<int>) returns (result: int)
    requires ValidInput(diameters)
    ensures result == num_distinct(diameters)
    ensures result >= 1
    ensures result <= |diameters|
{
    var ds := diameters;
    var mochidan := 0;

    assert |diameters| > 0 ==> num_distinct(diameters) >= 1;

    while |ds| > 0
        invariant mochidan + num_distinct(ds) == num_distinct(diameters)
        invariant mochidan >= 0
        decreases |ds|
    {
        var tmp := max_seq(ds);
        assert tmp in ds;

        var ds_new := filter_not_equal(ds, tmp);
        lemma_remove_distinct_element(ds, tmp);
        assert num_distinct(ds) == 1 + num_distinct(ds_new);

        ds := ds_new;
        mochidan := mochidan + 1;
    }

    result := mochidan;
}
