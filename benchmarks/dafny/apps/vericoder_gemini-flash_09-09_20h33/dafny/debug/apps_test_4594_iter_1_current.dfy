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
function distinct_count_set(s: seq<int>): set<int>
  reads s
  ensures forall x :: x in distinct_count_set(s) <==> x in s
  ensures |distinct_count_set(s)| == num_distinct(s)
{
  if |s| == 0 then {}
  else {s[0]} + distinct_count_set(s[1..])
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
    var distinct_elements := new_HashSet();
    for i := 0 to |diameters| - 1
        invariant 0 <= i <= |diameters|
        invariant distinct_elements.ContainsAll(distinct_count_set(diameters[0 .. i]))
        invariant forall x :: x in distinct_elements.Elements() ==> x in diameters[0 .. i]
    {
        distinct_elements.Add(diameters[i]);
    }
    result := distinct_elements.Size();
}
// </vc-code>

