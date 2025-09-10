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
    else (
          var max_dist := 0;
          for i := 0 to |placement| - 2
              invariant 0 <= i < |placement| - 1
              invariant max_dist == (max j | 0 <= j <= i :: placement[j+1] - placement[j])
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
        invariant forall j :: 0 <= j < zero_count ==> zeros[j] < n
        invariant forall j :: 0 <= j < zero_count ==> (exists k_ :: 0 <= k_ < n && rooms[k_] == '0' && zeros[j] == k_)
        invariant forall j, l :: 0 <= j < l < zero_count ==> zeros[j] < zeros[l]
        invariant (forall k_ | 0 <= k_ < i && rooms[k_] == '0' :: (exists j | 0 <= j < zero_count :: zeros[j] == k_))
        invariant (forall j | 0 <= j < zero_count :: (exists k_ | 0 <= k_ < i && rooms[k_] == '0' :: zeros[j] == k_))
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
        invariant (forall d' | 0 <= d' < result_dist :: (forall placement_ :: !(isValidPlacement(rooms, k, placement_) && optimalMaxDistance(placement_) <= d')))
        invariant (forall d' | low <= d' <= result_dist :: exists placement_ :: isValidPlacement(rooms, k, placement_) && optimalMaxDistance(placement_) <= d')
        invariant (forall d' | (high < d' && d' > result_dist) :: forall placement_ :: !(isValidPlacement(rooms,k,placement_) && optimalMaxDistance(placement_) <= d'))
        invariant low <= n + 1
        invariant high <= n
    {
        var mid := low + (high - low) / 2;
        if mid == 0 {
            if k == 0 { // If k is 0, we need 1 room. The max distance is 0 if we can pick any single '0'.
                result_dist := max(result_dist, mid);
                low := mid + 1;
            } else { // if k > 0 and mid = 0, we can only place if all zeros are adjacent, which is rarely true
                high := mid - 1;
            }
            continue;
        }
        
        var current_available_zeros := 0;
        var last_zero_idx := -mid; // Initialize so first zero always gets picked
        var valid_placement_found := false;
        
        var j_start := 0;
        while j_start < zero_count && zeros[j_start] < mid
            invariant 0 <= j_start <= zero_count
            invariant (forall x | 0 <= x < j_start :: zeros[x] < mid)
        {
            j_start := j_start + 1;
        }
        
        var j := 0;
        var chosen_cnt := 0;
        var current_placement: seq<int> := [];

        while j < zero_count
            invariant 0 <= j <= zero_count
            invariant chosen_cnt <= k + 1
            invariant |current_placement| == chosen_cnt
            invariant forall l :: 0 <= l < chosen_cnt ==> rooms[current_placement[l]] == '0'
            invariant forall l :: 0 <= l < chosen_cnt ==> current_placement[l] == zeros[j] || current_placement[l] < zeros[j]
            invariant forall l :: 0 <= l < chosen_cnt - 1 ==> current_placement[l] < current_placement[l+1]
            invariant (current_placement == [] ==> true) || optimalMaxDistance(current_placement) <= mid
        {
            if current_placement == [] {
                if chosen_cnt < k + 1 {
                    current_placement := current_placement + [zeros[j]];
                    chosen_cnt := chosen_cnt + 1;
                }
            } else if zeros[j] - current_placement[chosen_cnt - 1] >= mid {
                if chosen_cnt < k + 1 {
                    current_placement := current_placement + [zeros[j]];
                    chosen_cnt := chosen_cnt + 1;
                }
            }
            j := j + 1;
        }

        if chosen_cnt >= k + 1 {
            result_dist := max(result_dist, mid);
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
    result := result_dist;
}
// </vc-code>

