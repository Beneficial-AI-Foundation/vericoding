predicate ValidInput(n: int, k: int, a: int, m: int, shots: seq<int>)
{
    n > 0 && k > 0 && a > 0 && m > 0 && |shots| == m &&
    (forall i :: 0 <= i < |shots| ==> 1 <= shots[i] <= n)
}

function canPlaceShipsFunc(n: int, k: int, a: int, shots: seq<int>, numShots: int): bool
    requires n > 0 && k > 0 && a > 0 && numShots >= 0
    requires numShots <= |shots|
    requires forall i :: 0 <= i < |shots| ==> 1 <= shots[i] <= n
{
    var hitCells := set i | 0 <= i < numShots && i < |shots| :: shots[i];
    greedyShipPlacement(n, k, a, hitCells) >= k
}

function greedyShipPlacement(n: int, k: int, a: int, hitCells: set<int>): int
    requires n > 0 && k > 0 && a > 0
    requires forall cell :: cell in hitCells ==> 1 <= cell <= n
{
    greedyPlaceShipsFromPosition(1, n, k, a, hitCells)
}

function greedyPlaceShipsFromPosition(pos: int, n: int, k: int, a: int, hitCells: set<int>): int
    requires pos >= 1 && n > 0 && k >= 0 && a > 0
    requires forall cell :: cell in hitCells ==> 1 <= cell <= n
    decreases n - pos + 1, k
{
    if pos > n || k == 0 then 0
    else if pos + a - 1 <= n && forall cell :: pos <= cell <= pos + a - 1 ==> cell !in hitCells then
        1 + greedyPlaceShipsFromPosition(pos + a + 1, n, k - 1, a, hitCells)
    else
        greedyPlaceShipsFromPosition(pos + 1, n, k, a, hitCells)
}

predicate isNaturalNumberString(str: string)
{
    |str| > 0 && str[0] != '0' && forall i :: 0 <= i < |str| ==> '0' <= str[i] <= '9'
}

function parseInputSpec(input: string): seq<string>
    requires |input| > 0
    ensures |parseInputSpec(input)| >= 0
{
    []
}

function parseThreeIntsSpec(line: string): (int, int, int)
    ensures parseThreeIntsSpec(line).0 > 0 && parseThreeIntsSpec(line).1 > 0 && parseThreeIntsSpec(line).2 > 0
{
    (1, 1, 1)
}

function parseIntSpec(line: string): int
    ensures parseIntSpec(line) >= 0
{
    0
}

function parseIntArraySpec(line: string): seq<int>
    ensures forall i :: 0 <= i < |parseIntArraySpec(line)| ==> parseIntArraySpec(line)[i] > 0
{
    []
}

function intToStringSpec(value: int): string
    requires value >= 1
    ensures |intToStringSpec(value)| > 0
    ensures isNaturalNumberString(intToStringSpec(value))
{
    "1"
}

// <vc-helpers>
lemma CanPlaceShipsMonotonic(n: int, k: int, a: int, shots: seq<int>, i: int, j: int)
    requires n > 0 && k > 0 && a > 0
    requires 0 <= i <= j <= |shots|
    requires forall idx :: 0 <= idx < |shots| ==> 1 <= shots[idx] <= n
    ensures !canPlaceShipsFunc(n, k, a, shots, j) ==> !canPlaceShipsFunc(n, k, a, shots, i)
{
    // The key insight: hitCells(i) ⊆ hitCells(j) when i <= j
    var hitCellsI := set idx | 0 <= idx < i && idx < |shots| :: shots[idx];
    var hitCellsJ := set idx | 0 <= idx < j && idx < |shots| :: shots[idx];
    
    // Prove that hitCellsI is a subset of hitCellsJ
    assert forall cell :: cell in hitCellsI ==> cell in hitCellsJ;
    
    // Use the helper lemma to show greedyShipPlacement is monotonic
    GreedyPlacementMonotonic(n, k, a, hitCellsI, hitCellsJ);
    
    // Connect the definitions
    assert canPlaceShipsFunc(n, k, a, shots, i) == (greedyShipPlacement(n, k, a, hitCellsI) >= k);
    assert canPlaceShipsFunc(n, k, a, shots, j) == (greedyShipPlacement(n, k, a, hitCellsJ) >= k);
}

lemma GreedyPlacementMonotonic(n: int, k: int, a: int, hitCells1: set<int>, hitCells2: set<int>)
    requires n > 0 && k > 0 && a > 0
    requires forall cell :: cell in hitCells1 ==> 1 <= cell <= n
    requires forall cell :: cell in hitCells2 ==> 1 <= cell <= n
    requires hitCells1 <= hitCells2  // hitCells1 is a subset of hitCells2
    ensures greedyShipPlacement(n, k, a, hitCells1) >= greedyShipPlacement(n, k, a, hitCells2)
{
    GreedyPlacementFromPositionMonotonic(1, n, k, a, hitCells1, hitCells2);
}

lemma GreedyPlacementFromPositionMonotonic(pos: int, n: int, k: int, a: int, hitCells1: set<int>, hitCells2: set<int>)
    requires pos >= 1 && n > 0 && k >= 0 && a > 0
    requires forall cell :: cell in hitCells1 ==> 1 <= cell <= n
    requires forall cell :: cell in hitCells2 ==> 1 <= cell <= n
    requires hitCells1 <= hitCells2
    ensures greedyPlaceShipsFromPosition(pos, n, k, a, hitCells1) >= greedyPlaceShipsFromPosition(pos, n, k, a, hitCells2)
    decreases n - pos + 1, k
{
    if pos > n || k == 0 {
        // Base case: both return 0
    } else {
        var canPlace1 := pos + a - 1 <= n && forall cell :: pos <= cell <= pos + a - 1 ==> cell !in hitCells1;
        var canPlace2 := pos + a - 1 <= n && forall cell :: pos <= cell <= pos + a - 1 ==> cell !in hitCells2;
        
        if canPlace1 && canPlace2 {
            // Both can place a ship at this position
            GreedyPlacementFromPositionMonotonic(pos + a + 1, n, k - 1, a, hitCells1, hitCells2);
        } else if canPlace1 && !canPlace2 {
            // Only hitCells1 can place a ship (fewer hits)
            GreedyPlacementFromPositionMonotonic(pos + a + 1, n, k - 1, a, hitCells1, hitCells2);
            GreedyPlacementFromPositionMonotonic(pos + 1, n, k, a, hitCells1, hitCells2);
            assert greedyPlaceShipsFromPosition(pos, n, k, a, hitCells1) == 
                   1 + greedyPlaceShipsFromPosition(pos + a + 1, n, k - 1, a, hitCells1);
            assert greedyPlaceShipsFromPosition(pos, n, k, a, hitCells2) == 
                   greedyPlaceShipsFromPosition(pos + 1, n, k, a, hitCells2);
        } else {
            // Neither can place a ship at this position
            GreedyPlacementFromPositionMonotonic(pos + 1, n, k, a, hitCells1, hitCells2);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n'
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures result == "-1\n" || (exists shot_num_str :: |shot_num_str| > 0 && result == shot_num_str + "\n" && isNaturalNumberString(shot_num_str))
    ensures var lines := parseInputSpec(stdin_input);
            if |lines| >= 3 then
                var firstLine := parseThreeIntsSpec(lines[0]);
                var n, k, a := firstLine.0, firstLine.1, firstLine.2;
                var m := parseIntSpec(lines[1]);
                var shots := parseIntArraySpec(lines[2]);
                if ValidInput(n, k, a, m, shots) then
                    if canPlaceShipsFunc(n, k, a, shots, m) then
                        result == "-1\n"
                    else
                        exists shot_idx :: 1 <= shot_idx <= m && 
                                         result == intToStringSpec(shot_idx) + "\n" &&
                                         !canPlaceShipsFunc(n, k, a, shots, shot_idx) &&
                                         (shot_idx == 1 || canPlaceShipsFunc(n, k, a, shots, shot_idx-1))
                else
                    true
            else
                true
// </vc-spec>
// <vc-code>
{
    var lines := parseInputSpec(stdin_input);
    
    if |lines| < 3 {
        return "-1\n";
    }
    
    var firstLine := parseThreeIntsSpec(lines[0]);
    var n, k, a := firstLine.0, firstLine.1, firstLine.2;
    var m := parseIntSpec(lines[1]);
    var shots := parseIntArraySpec(lines[2]);
    
    if !ValidInput(n, k, a, m, shots) {
        return "-1\n";
    }
    
    // Check if we can place ships after all m shots
    if canPlaceShipsFunc(n, k, a, shots, m) {
        return "-1\n";
    }
    
    // Binary search to find the first shot that makes placement impossible
    var left := 1;
    var right := m;
    
    while left < right
        invariant 1 <= left <= right <= m
        invariant !canPlaceShipsFunc(n, k, a, shots, right)
        invariant left == 1 || canPlaceShipsFunc(n, k, a, shots, left - 1)
        decreases right - left
    {
        var mid := (left + right) / 2;
        
        if canPlaceShipsFunc(n, k, a, shots, mid) {
            left := mid + 1;
        } else {
            CanPlaceShipsMonotonic(n, k, a, shots, mid, right);
            right := mid;
        }
    }
    
    // At this point, left == right and is the first shot index where placement fails
    var shot_num_str := intToStringSpec(left);
    result := shot_num_str + "\n";
}
// </vc-code>

