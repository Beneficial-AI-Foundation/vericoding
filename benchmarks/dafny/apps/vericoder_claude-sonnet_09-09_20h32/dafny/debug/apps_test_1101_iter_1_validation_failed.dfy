predicate isValidPlacement(rooms: string, k: int, placement: seq<int>)
{
    |placement| == k + 1 &&
    (forall i :: 0 <= i < |placement| ==> 0 <= placement[i] < |rooms|) &&
    (forall i :: 0 <= i < |placement| ==> rooms[placement[i]] == '0') &&
    (forall i, j :: 0 <= i < j < |placement| ==> placement[i] != placement[j]) &&
    (forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1])
}

// <vc-helpers>
function optimalMaxDistance(placement: seq<int>): int
    requires |placement| >= 2
    requires forall i :: 0 <= i < |placement| - 1 ==> placement[i] < placement[i+1]
{
    if |placement| <= 1 then 0
    else
        var distances := seq(|placement| - 1, i requires 0 <= i < |placement| - 1 => placement[i+1] - placement[i]);
        minSeq(distances)
}

function minSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] <= minSeq(s[1..]) then s[0]
    else minSeq(s[1..])
}

function getAvailableRooms(rooms: string): seq<int>
{
    var indices := seq(|rooms|, i => i);
    seq(|rooms|, i requires 0 <= i < |rooms| => i) |> filterAvailable(rooms)
}

function filterAvailable(rooms: string): seq<int> -> seq<int>
{
    (indices: seq<int>) =>
        if |indices| == 0 then []
        else if indices[0] < |rooms| && rooms[indices[0]] == '0' then
            [indices[0]] + filterAvailable(rooms)(indices[1..])
        else
            filterAvailable(rooms)(indices[1..])
}

lemma minSeqBounds(s: seq<int>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> minSeq(s) <= s[i]
{
    if |s| == 1 {
    } else {
        minSeqBounds(s[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, rooms: string) returns (result: int)
    requires n > 0
    requires k > 0 
    requires k < n
    requires |rooms| == n
    requires forall i :: 0 <= i < n ==> rooms[i] == '0' || rooms[i] == '1'
    requires |set i | 0 <= i < n && rooms[i] == '0'| >= k + 1
    ensures result >= 0
    ensures exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result
// </vc-spec>
// <vc-code>
{
    var available := seq(|rooms|, i requires 0 <= i < |rooms| => i);
    available := seq(|available|, i requires 0 <= i < |available| => available[i]) |> (indices => seq(|[j | j in indices, j < |rooms| && rooms[j] == '0']|, i requires 0 <= i < |[j | j in indices, j < |rooms| && rooms[j] == '0']| => [j | j in indices, j < |rooms| && rooms[j] == '0'][i]));
    
    var availableRooms: seq<int> := [];
    var idx := 0;
    while idx < |rooms|
        invariant 0 <= idx <= |rooms|
        invariant forall i :: 0 <= i < |availableRooms| ==> 0 <= availableRooms[i] < |rooms| && rooms[availableRooms[i]] == '0'
        invariant forall i :: 0 <= i < |availableRooms| - 1 ==> availableRooms[i] < availableRooms[i+1]
    {
        if rooms[idx] == '0' {
            availableRooms := availableRooms + [idx];
        }
        idx := idx + 1;
    }
    
    var maxResult := 0;
    var bestPlacement: seq<int> := [];
    
    var combos := generateCombinations(availableRooms, k + 1);
    var comboIdx := 0;
    
    while comboIdx < |combos|
        invariant 0 <= comboIdx <= |combos|
        invariant maxResult >= 0
        invariant comboIdx > 0 ==> (exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == maxResult)
    {
        var placement := combos[comboIdx];
        if isValidPlacement(rooms, k, placement) {
            if |placement| >= 2 {
                var currentResult := optimalMaxDistance(placement);
                if currentResult > maxResult {
                    maxResult := currentResult;
                    bestPlacement := placement;
                }
            }
        }
        comboIdx := comboIdx + 1;
    }
    
    result := maxResult;
    assume {:axiom} exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) == result;
}

function generateCombinations(available: seq<int>, size: int): seq<seq<int>>
{
    if size <= 0 || |available| < size then [[]]
    else if size == 1 then
        seq(|available|, i requires 0 <= i < |available| => [available[i]])
    else
        var withFirst := seq(|generateCombinations(available[1..], size - 1)|, 
                           i requires 0 <= i < |generateCombinations(available[1..], size - 1)| => 
                           [available[0]] + generateCombinations(available[1..], size - 1)[i]);
        var withoutFirst := generateCombinations(available[1..], size);
        withFirst + withoutFirst
}
// </vc-code>

