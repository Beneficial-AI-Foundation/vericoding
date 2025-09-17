// <vc-preamble>

predicate ValidInput(grid: seq<seq<int>>, capacity: int)
{
    capacity > 0 &&
    (forall i :: 0 <= i < |grid| ==> forall j :: 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1) &&
    (forall i :: 0 <= i < |grid| ==> |grid[i]| == if |grid| > 0 then |grid[0]| else 0)
}

function sum_water(well: seq<int>): int
    requires forall j :: 0 <= j < |well| ==> well[j] == 0 || well[j] == 1
{
    if |well| == 0 then 0
    else well[0] + sum_water(well[1..])
}

function trips_for_well(well: seq<int>, capacity: int): int
    requires capacity > 0
    requires forall j :: 0 <= j < |well| ==> well[j] == 0 || well[j] == 1
{
    var water_units := sum_water(well);
    if water_units == 0 then 0
    else (water_units + capacity - 1) / capacity
}

function sum_of_trips(grid: seq<seq<int>>, capacity: int): int
    requires capacity > 0
    requires forall i :: 0 <= i < |grid| ==> forall j :: 0 <= j < |grid[i]| ==> grid[i][j] == 0 || grid[i][j] == 1
    requires forall i :: 0 <= i < |grid| ==> |grid[i]| == if |grid| > 0 then |grid[0]| else 0
{
    if |grid| == 0 then 0
    else trips_for_well(grid[0], capacity) + sum_of_trips(grid[1..], capacity)
}
lemma sum_water_slice_lemma(well: seq<int>, j: int)
    requires 0 <= j < |well|
    requires forall k :: 0 <= k < |well| ==> well[k] == 0 || well[k] == 1
    ensures sum_water(well[..j+1]) == sum_water(well[..j]) + well[j]
{
    if j == 0 {
        assert well[..1] == [well[0]];
        assert well[..0] == [];
        assert sum_water(well[..0]) == 0;
        assert sum_water(well[..1]) == well[0] + sum_water([]);
        assert sum_water(well[..1]) == well[0] + 0;
        assert sum_water(well[..1]) == well[0];
    } else {
        assert well[..j+1] == well[..j] + [well[j]];
        assert sum_water(well[..j+1]) == well[0] + sum_water((well[..j+1])[1..]);
        assert (well[..j+1])[1..] == well[1..j+1];
        assert well[1..j+1] == (well[1..])[..j];
        sum_water_slice_lemma(well[1..], j-1);
        assert sum_water((well[1..])[..j]) == sum_water((well[1..])[..j-1]) + (well[1..])[j-1];
        assert (well[1..])[j-1] == well[j];
        assert sum_water(well[..j]) == well[0] + sum_water((well[..j])[1..]);
        assert (well[..j])[1..] == well[1..j];
        assert well[1..j] == (well[1..])[..j-1];
        assert sum_water(well[..j]) == well[0] + sum_water((well[1..])[..j-1]);
        assert sum_water(well[..j+1]) == well[0] + sum_water((well[1..])[..j]);
        assert sum_water(well[..j+1]) == well[0] + sum_water((well[1..])[..j-1]) + well[j];
        assert sum_water(well[..j+1]) == sum_water(well[..j]) + well[j];
    }
}

lemma sum_water_full_slice_lemma(well: seq<int>)
    requires forall j :: 0 <= j < |well| ==> well[j] == 0 || well[j] == 1
    ensures sum_water(well[..|well|]) == sum_water(well)
{
    assert well[..|well|] == well;
}

lemma sum_of_trips_slice_lemma(grid: seq<seq<int>>, i: int, capacity: int)
    requires capacity > 0
    requires 0 <= i < |grid|
    requires forall k :: 0 <= k < |grid| ==> forall j :: 0 <= j < |grid[k]| ==> grid[k][j] == 0 || grid[k][j] == 1
    requires forall k :: 0 <= k < |grid| ==> |grid[k]| == if |grid| > 0 then |grid[0]| else 0
    ensures sum_of_trips(grid[..i+1], capacity) == sum_of_trips(grid[..i], capacity) + trips_for_well(grid[i], capacity)
{
    if i == 0 {
        assert grid[..1] == [grid[0]];
        assert grid[..0] == [];
        assert sum_of_trips(grid[..0], capacity) == 0;
        assert sum_of_trips(grid[..1], capacity) == trips_for_well(grid[0], capacity) + sum_of_trips([], capacity);
        assert sum_of_trips(grid[..1], capacity) == trips_for_well(grid[0], capacity) + 0;
    } else {
        assert grid[..i+1] == [grid[0]] + grid[1..i+1];
        assert sum_of_trips(grid[..i+1], capacity) == trips_for_well(grid[0], capacity) + sum_of_trips(grid[1..i+1], capacity);
        assert grid[1..i+1] == (grid[1..])[..i];
        sum_of_trips_slice_lemma(grid[1..], i-1, capacity);
        assert sum_of_trips((grid[1..])[..i], capacity) == sum_of_trips((grid[1..])[..i-1], capacity) + trips_for_well((grid[1..])[i-1], capacity);
        assert (grid[1..])[i-1] == grid[i];
        assert grid[..i] == [grid[0]] + grid[1..i];
        assert sum_of_trips(grid[..i], capacity) == trips_for_well(grid[0], capacity) + sum_of_trips(grid[1..i], capacity);
        assert grid[1..i] == (grid[1..])[..i-1];
        assert sum_of_trips(grid[..i], capacity) == trips_for_well(grid[0], capacity) + sum_of_trips((grid[1..])[..i-1], capacity);
        assert sum_of_trips(grid[1..i+1], capacity) == sum_of_trips((grid[1..])[..i-1], capacity) + trips_for_well(grid[i], capacity);
        assert sum_of_trips(grid[..i+1], capacity) == trips_for_well(grid[0], capacity) + sum_of_trips((grid[1..])[..i-1], capacity) + trips_for_well(grid[i], capacity);
        assert sum_of_trips(grid[..i+1], capacity) == sum_of_trips(grid[..i], capacity) + trips_for_well(grid[i], capacity);
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method max_fill(grid: seq<seq<int>>, capacity: int) returns (result: int)
    requires ValidInput(grid, capacity)
    ensures result >= 0
    ensures result == sum_of_trips(grid, capacity)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
