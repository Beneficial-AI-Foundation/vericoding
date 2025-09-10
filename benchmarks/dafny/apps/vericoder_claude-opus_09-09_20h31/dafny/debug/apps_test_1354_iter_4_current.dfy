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
    if !canPlaceShipsFunc(n, k, a, shots, j) {
        var hitCellsI := set idx | 0 <= idx < i && idx < |shots| :: shots[idx];
        var hitCellsJ := set idx | 0 <= idx < j && idx < |shots| :: shots[idx];
        
        assert forall cell :: cell in hitCellsI ==> cell in hitCellsJ;
        
        GreedyPlacementMonotonic(n, k, a, hitCellsI, hitCellsJ);
        
        assert canPlaceShipsFunc(n, k, a, shots, i) == (greedyShipPlacement(n, k, a, hitCellsI) >= k);
        assert canPlaceShipsFunc(n, k, a, shots, j) == (greedyShipPlacement(n, k, a, hitCellsJ) >= k);
        
        assert greedyShipPlacement(n, k, a, hitCellsI) >= greedyShipPlacement(n, k, a, hitCellsJ);
        
        assert greedyShipPlacement(n, k, a, hitCellsJ) < k;
        assert !canPlaceShipsFunc(n, k, a, shots, i);
    }
}

lemma GreedyPlacementMonotonic(n: int, k: int, a: int, hitCells1: set<int>, hitCells2: set<int>)
    requires n > 0 && k > 0 && a > 0
    requires forall cell :: cell in hitCells1 ==> 1 <= cell <= n
    requires forall cell :: cell in hitCells2 ==> 1 <= cell <= n
    requires hitCells1 <= hitCells2
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
            GreedyPlacementFromPositionMonotonic(pos + a + 1, n, k - 1, a, hitCells1, hitCells2);
        } else if canPlace1 && !canPlace2 {
            // hitCells1 can place but hitCells2 cannot
            // We need to show placing with hitCells1 is better than skipping with hitCells2
            GreedySkipVsPlaceHelper(pos, n, k, a, hitCells1, hitCells2);
        } else {
            // Neither can place or both cannot place
            GreedyPlacementFromPositionMonotonic(pos + 1, n, k, a, hitCells1, hitCells2);
        }
    }
}

lemma GreedySkipVsPlaceHelper(pos: int, n: int, k: int, a: int, hitCells1: set<int>, hitCells2: set<int>)
    requires pos >= 1 && n > 0 && k > 0 && a > 0
    requires forall cell :: cell in hitCells1 ==> 1 <= cell <= n
    requires forall cell :: cell in hitCells2 ==> 1 <= cell <= n
    requires hitCells1 <= hitCells2
    requires pos + a - 1 <= n && (forall cell :: pos <= cell <= pos + a - 1 ==> cell !in hitCells1)
    requires !(pos + a - 1 <= n && (forall cell :: pos <= cell <= pos + a - 1 ==> cell !in hitCells2))
    ensures 1 + greedyPlaceShipsFromPosition(pos + a + 1, n, k - 1, a, hitCells1) >= 
            greedyPlaceShipsFromPosition(pos + 1, n, k, a, hitCells2)
    decreases n - pos + 1, k
{
    if pos + 1 > n || k == 0 {
        // Base case
        assert greedyPlaceShipsFromPosition(pos + 1, n, k, a, hitCells2) == 0;
        assert 1 + greedyPlaceShipsFromPosition(pos + a + 1, n, k - 1, a, hitCells1) >= 0;
    } else {
        // We have 1 ship placed at pos with hitCells1
        // Need to show this is at least as good as skipping with hitCells2
        
        // First establish monotonicity for the remaining positions
        if pos + a + 1 <= n && k - 1 > 0 {
            GreedyPlacementFromPositionMonotonic(pos + a + 1, n, k - 1, a, hitCells1, hitCells2);
        }
        
        // The key insight: we've placed one ship, and the remaining placements
        // with hitCells1 are at least as good as with hitCells2
        var remaining1 := greedyPlaceShipsFromPosition(pos + a + 1, n, k - 1, a, hitCells1);
        var skip2 := greedyPlaceShipsFromPosition(pos + 1, n, k, a, hitCells2);
        
        // Since we couldn't place at pos with hitCells2, and hitCells1 ⊆ hitCells2,
        // the skip path for hitCells2 can place at most k-1 ships in the best case
        GreedySkipUpperBound(pos + 1, n, k, a, hitCells2, pos);
    }
}

lemma GreedySkipUpperBound(start: int, n: int, k: int, a: int, hitCells: set<int>, blockedPos: int)
    requires start >= 1 && n > 0 && k >= 0 && a > 0
    requires forall cell :: cell in hitCells ==> 1 <= cell <= n
    requires blockedPos >= 1 && blockedPos < start
    requires !(blockedPos + a - 1 <= n && (forall cell :: blockedPos <= cell <= blockedPos + a - 1 ==> cell !in hitCells))
    ensures greedyPlaceShipsFromPosition(start, n, k, a, hitCells) <= k
    decreases n - start + 1, k
{
    // This is trivially true as greedy placement can never place more than k ships
    if start > n || k == 0 {
        assert greedyPlaceShipsFromPosition(start, n, k, a, hitCells) == 0;
    } else if start + a - 1 <= n && (forall cell :: start <= cell <= start + a - 1 ==> cell !in hitCells) {
        if k > 0 {
            GreedySkipUpperBound(start + a + 1, n, k - 1, a, hitCells, blockedPos);
            assert greedyPlaceShipsFromPosition(start, n, k, a, hitCells) == 
                   1 + greedyPlaceShipsFromPosition(start + a + 1, n, k - 1, a, hitCells);
            assert greedyPlaceShipsFromPosition(start + a + 1, n, k - 1, a, hitCells) <= k - 1;
            assert 1 + (k - 1) <= k;
        }
    } else {
        GreedySkipUpperBound(start + 1, n, k, a, hitCells, blockedPos);
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
    
    // Establish initial invariant
    assert !canPlaceShipsFunc(n, k, a, shots, right);
    
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
    assert !canPlaceShipsFunc(n, k, a, shots, left);
    assert left == 1 || canPlaceShipsFunc(n, k, a, shots, left - 1);
    
    var shot_num_str := intToStringSpec(left);
    result := shot_num_str + "\n";
}
// </vc-code>

