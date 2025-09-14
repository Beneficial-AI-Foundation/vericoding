predicate ValidInput(magnets: seq<string>)
{
    forall i :: 0 <= i < |magnets| ==> magnets[i] in {"01", "10"}
}

function CountGroups(magnets: seq<string>) : int
    requires ValidInput(magnets)
{
    if |magnets| == 0 then 0
    else 1 + |set i | 1 <= i < |magnets| && magnets[i] != magnets[i-1]|
}

// <vc-helpers>
lemma CountGroupsSlice(magnets: seq<string>, start: int, end: int)
    requires ValidInput(magnets)
    requires 0 <= start <= end <= |magnets|
    ensures CountGroups(magnets[start..end]) == 
        if start == end then 0 
        else 1 + |(set j | start < j < end && magnets[j] != magnets[j-1])|
{
    if start == end {
        calc {
            CountGroups(magnets[start..end]);
            CountGroups(magnets[start..start]);
            { assert magnets[start..start] == []; }
            CountGroups([]);
            0;
        }
    } else {
        calc {
            CountGroups(magnets[start..end]);
            { assert magnets[start..end] == [magnets[start]] + magnets[start+1..end]; }
            if |[magnets[start]] + magnets[start+1..end]| == 0 then 0
            else 1 + |(set i | 1 <= i < |[magnets[start]] + magnets[start+1..end]| && 
                           ([magnets[start]] + magnets[start+1..end])[i] != ([magnets[start]] + magnets[start+1..end])[i-1])|;
            { assert|[magnets[start]] + magnets[start+1..end]| == 1 + |magnets[start+1..end]|; }
            1 + |(set i | 1 <= i < 1 + |magnets[start+1..end]| && 
                   ([magnets[start]] + magnets[start+1..end])[i] != ([magnets[start]] + magnets[start+1..end])[i-1])|;
            { assert forall i: int :: 1 <= i < 1 + |magnets[start+1..end]| ==> 
                  ([magnets[start]] + magnets[start+1..end])[i] == magnets[start+1..end][i-1]; }
            1 + |(set i | 1 <= i < 1 + |magnets[start+1..end]| && 
                   magnets[start+1..end][i-1] != magnets[start+1..end][i-2])|;
            { assert var s := set j: int :: 1 <= j < |magnets[start+1..end]| && magnets[start+1..end][j] != magnets[start+1..end][j-1];
                  var t := set i: int :: 1 <= i < 1 + |magnets[start+1..end]| && magnets[start+1..end][i-1] != magnets[start+1..end][i-2];
                  s == t; }
            1 + |(set j | 1 <= j < |magnets[start+1..end]| && magnets[start+1..end][j] != magnets[start+1..end][j-1])|;
            { forall j | 1 <= j < |magnets[start+1..end]| ::
                  magnets[start+1..end][j] != magnets[start+1..end][j-1] <==> 
                  magnets[start+1+j] != magnets[start+1+j-1];
            }
            1 + |(set j | 1 <= j < |magnets[start+1..end]| && 
                   magnets[start+1+j] != magnets[start+1+j-1])|;
            { assert |magnets[start+1..end]| == end - start - 1; }
            { forall j: int :: 1 <= j < end - start - 1 ==> 
                start+1+j in [start+2, end) && start+1+j-1 in [start+1, end-1]; }
            1 + |(set j | start+1 < j < end && magnets[j] != magnets[j-1])|;
            { assert var s := set j: int :: start+1 < j < end && magnets[j] != magnets[j-1];
                  var t := set j: int :: start < j < end && magnets[j] != magnets[j-1];
                  s == t - (if start+1 < start && magnets[start] != magnets[start-1] then {start} else {});
                  s == t;
            }
            1 + |(set j | start < j < end && magnets[j] != magnets[j-1])|;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(magnets: seq<string>) returns (result: int)
    requires ValidInput(magnets)
    ensures result >= 0
    ensures |magnets| == 0 ==> result == 0
    ensures |magnets| > 0 ==> result >= 1
    ensures result <= |magnets|
    ensures result == CountGroups(magnets)
// </vc-spec>
// <vc-code>
{
    return CountGroups(magnets);
}
// </vc-code>

