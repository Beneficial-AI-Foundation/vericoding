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
{
    if |placement| <= 1 then 0
    else (var max_dist := 0; 
          for i := 0 to |placement| - 2
              invariant 0 <= i < |placement|-1
              invariant max_dist == (if i == 0 then 0 else (max j | 0 <= j < i :: placement[j+1] - placement[j]))
          {
              max_dist := max(max_dist, placement[i+1] - placement[i]);
          }
          return max_dist;
         )
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
    var max_dist := 0;
    var zeros := new int[n];
    var zero_count := 0;
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant 0 <= zero_count <= i
        invariant forall j :: 0 <= j < zero_count ==> rooms[zeros[j]] == '0'
        invariant forall j :: 0 <= j < zero_count ==> zeros[j] == (min x | 0 <= x < n && rooms[x] == '0' && (forall y | 0 <= y < x :: rooms[y] == '1' || (exists l | 0 <= l < j :: zeros[l] == y)) :: x)
        invariant forall j, l :: 0 <= j < l < zero_count ==> zeros[j] < zeros[l]
    {
        if rooms[i] == '0' {
            zeros[zero_count] := i;
            zero_count := zero_count + 1;
        }
    }

    // Binary search for the maximum distance
    var low := 0;
    var high := n; // Max possible distance between two adjacent ones is n-1
    var result_dist := 0;

    while low <= high
        invariant 0 <= low <= high + 1
        invariant 0 <= result_dist <= n
        invariant result_dist <= low
        invariant high < n + 1 // Maintain sense of current search space, high could be n or n-1 based on calculation
        // if a distance `d` fails (no valid placement), then any distance `d'` > `d` also fails.
        // if a distance `d` passes (valid placement exists), then any distance `d'` < `d` also passes.
        invariant (forall d' | low <= d' <= result_dist :: exists placement :: isValidPlacement(rooms, k, placement) && optimalMaxDistance(placement) <= d')
        invariant (forall d' | (high < d' && d' > result_dist) :: forall placement :: !(isValidPlacement(rooms,k,placement) && optimalMaxDistance(placement) <= d'))

    {
        var mid := low + (high - low) / 2;
        if mid == 0 { // special handling for mid=0, as it leads to division by zero for max_zeros_needed_for_dist calculation (target_dist_div)
            if k == 0 { // If k is 0, we need 1 room. The max distance is 0 if we can pick any single '0'.
                result_dist := max(result_dist, mid);
                low := mid + 1;
            } else { // if k > 0 and mid = 0, we can only place if all zeros are adjacent, which is rarely true
                high := mid - 1;
            }
            continue;
        }
        
        var current_available_zeros := 0;
        var last_zero_idx := -1;
        var valid_placement_found := false;

        var j := 0;
        while j < zero_count
            invariant 0 <= j <= zero_count
            invariant current_available_zeros <= k + 1
            invariant last_zero_idx == -1 || (0 <= last_zero_idx && last_zero_idx < n && rooms[last_zero_idx] == '0')
            // if last_zero_idx is -1, it means we haven't picked the first room yet.
            // if last_zero_idx is not -1, `current_available_zeros` counts the selected '0's starting from `last_zero_idx`.
            // These selected zeros form a valid `k_prime` segment such that `optimalMaxDistance(segment) <= mid`.
        {
            if last_zero_idx == -1 {
                last_zero_idx := zeros[j];
                current_available_zeros := 1;
            } else if zeros[j] - last_zero_idx >= mid {
                last_zero_idx := zeros[j];
                current_available_zeros := current_available_zeros + 1;
            }
            j := j + 1;
        }

        if current_available_zeros >= k + 1 {
            result_dist := max(result_dist, mid);
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    result := result_dist;
}
// </vc-code>

