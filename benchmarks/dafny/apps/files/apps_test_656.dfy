Given n winter days with temperature forecasts, minimize tire changes to drive safely.
Start with summer tires (safe when temp >= 0). Winter tires safe at any temp but 
limited to k days total. Must drive safely every day. Can change tires at start of any day.
Return minimum tire changes needed, or -1 if impossible.

function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}

lemma count_negative_temp_days_non_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) >= 0
{
    if |temps| == 0 {
        // Base case
    } else {
        count_negative_temp_days_non_negative(temps[1..]);
    }
}

lemma count_negative_temp_days_zero_iff_all_non_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) == 0 <==> (forall i :: 0 <= i < |temps| ==> temps[i] >= 0)
{
    if |temps| == 0 {
        // Base case: empty sequence
    } else {
        // Inductive case
        count_negative_temp_days_zero_iff_all_non_negative(temps[1..]);
        if temps[0] < 0 {
            // If first element is negative, count > 0 and not all are non-negative
            count_negative_temp_days_non_negative(temps[1..]);
            assert count_negative_temp_days(temps) == 1 + count_negative_temp_days(temps[1..]) >= 1;
            assert !(forall i :: 0 <= i < |temps| ==> temps[i] >= 0);
        } else {
            // If first element is non-negative, count is zero iff rest have count zero
            // and all non-negative iff first is non-negative and rest are non-negative
            assert temps[0] >= 0;
            assert count_negative_temp_days(temps) == 0 <==> count_negative_temp_days(temps[1..]) == 0;
            assert (forall i :: 0 <= i < |temps| ==> temps[i] >= 0) <==> (forall i :: 0 <= i < |temps[1..]| ==> temps[1..][i] >= 0);
        }
    }
}

lemma count_negative_temp_days_positive_iff_exists_negative(temps: seq<int>)
  ensures count_negative_temp_days(temps) > 0 <==> (exists i :: 0 <= i < |temps| && temps[i] < 0)
{
    if |temps| == 0 {
        // Base case: empty sequence
        assert count_negative_temp_days(temps) == 0;
        assert !(exists i :: 0 <= i < |temps| && temps[i] < 0);
    } else {
        // Inductive case
        count_negative_temp_days_positive_iff_exists_negative(temps[1..]);
        count_negative_temp_days_non_negative(temps[1..]);
        if temps[0] < 0 {
            // If first element is negative, count > 0 and there exists a negative
            assert count_negative_temp_days(temps) == 1 + count_negative_temp_days(temps[1..]) >= 1;
            assert exists i :: 0 <= i < |temps| && temps[i] < 0;
        } else {
            // If first element is non-negative, count > 0 iff rest have count > 0
            // and exists negative iff there exists negative in rest
            assert temps[0] >= 0;
            assert count_negative_temp_days(temps) > 0 <==> count_negative_temp_days(temps[1..]) > 0;
            assert (exists i :: 0 <= i < |temps| && temps[i] < 0) <==> (exists i :: 0 <= i < |temps[1..]| && temps[1..][i] < 0);
        }
    }
}

method solve(n: int, k: int, temps: seq<int>) returns (result: int)
  requires n >= 1
  requires k >= 0 && k <= n
  requires |temps| == n
  requires forall i :: 0 <= i < n ==> -20 <= temps[i] <= 20
  ensures result == -1 <==> count_negative_temp_days(temps) > k
  ensures result != -1 ==> result >= 0
  ensures result == 0 ==> forall i :: 0 <= i < n ==> temps[i] >= 0
  ensures result > 0 ==> exists i :: 0 <= i < n && temps[i] < 0
{
    if n == 0 {
        return 0;
    }

    // Count negative temperature days
    var neg_days := count_negative_temp_days(temps);
    count_negative_temp_days_non_negative(temps);

    if neg_days > k {
        return -1;
    }

    // If no negative days, we can use summer tires throughout
    if neg_days == 0 {
        assert forall i :: 0 <= i < n ==> temps[i] >= 0 by {
            count_negative_temp_days_zero_iff_all_non_negative(temps);
        }
        return 0;
    }

    assert neg_days > 0 by {
        count_negative_temp_days_non_negative(temps);
        assert neg_days != 0;
    }
    assert exists i :: 0 <= i < n && temps[i] < 0 by {
        count_negative_temp_days_positive_iff_exists_negative(temps);
    }

    var summer_seqs: seq<int> := [];
    var winter_seqs: seq<int> := [];

    var cur_season := 1; // 1 for summer, -1 for winter
    var cur_len := 0;

    var i := 0;
    while i < n {
        var t := temps[i];
        if (cur_season * t > 0) || (t == 0 && cur_season == 1) {
            cur_len := cur_len + 1;
        } else {
            if cur_season == 1 {
                summer_seqs := summer_seqs + [cur_len];
            } else {
                winter_seqs := winter_seqs + [cur_len];
            }
            cur_len := 1;
            cur_season := -cur_season;
        }
        i := i + 1;
    }

    if cur_season == 1 {
        summer_seqs := summer_seqs + [cur_len];
    } else {
        winter_seqs := winter_seqs + [cur_len];
    }

    // Remove first summer sequence since we start with summer tires
    if |summer_seqs| > 0 {
        summer_seqs := summer_seqs[1..];
    }

    if |summer_seqs| == 0 {
        if |winter_seqs| == 0 {
            return 1;
        } else {
            return 1;
        }
    }

    var changes := |summer_seqs| + |winter_seqs|;

    var last_sum_seq: int := -1;
    var has_last_sum_seq := false;
    if temps[n-1] >= 0 {
        has_last_sum_seq := true;
        last_sum_seq := summer_seqs[|summer_seqs|-1];
        summer_seqs := summer_seqs[..|summer_seqs|-1];
    }

    // Sort summer sequences (simple bubble sort with bounds checking)
    var sorted_summer := summer_seqs;
    var len := |sorted_summer|;
    i := 0;
    while i < len {
        var j := 0;
        while j < len - 1 && j + 1 < |sorted_summer| {
            if sorted_summer[j] > sorted_summer[j+1] {
                var temp := sorted_summer[j];
                sorted_summer := sorted_summer[j := sorted_summer[j+1]];
                sorted_summer := sorted_summer[j+1 := temp];
            }
            j := j + 1;
        }
        i := i + 1;
    }

    var total_winter_days := 0;
    i := 0;
    while i < |winter_seqs| {
        total_winter_days := total_winter_days + winter_seqs[i];
        i := i + 1;
    }

    var cur_winter_usage := total_winter_days;

    i := 0;
    while i < |sorted_summer| {
        if k - cur_winter_usage >= sorted_summer[i] {
            changes := changes - 2;
            cur_winter_usage := cur_winter_usage + sorted_summer[i];
        } else {
            break;
        }
        i := i + 1;
    }

    if has_last_sum_seq && k - cur_winter_usage >= last_sum_seq {
        changes := changes - 1;
    }

    return if changes >= 1 then changes else 1;
}
