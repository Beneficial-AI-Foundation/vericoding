predicate ValidInput(n: int, t: int, routes: seq<(int, int)>)
{
  n > 0 && |routes| == n && 
  forall i :: 0 <= i < n ==> routes[i].1 > 0
}

function getNextArrivalTime(firstTime: int, interval: int, targetTime: int): int
  requires interval > 0
{
  if firstTime >= targetTime then firstTime
  else firstTime + ((targetTime - firstTime + interval - 1) / interval) * interval
}

predicate IsOptimalRoute(routes: seq<(int, int)>, t: int, routeIndex: int)
  requires 0 <= routeIndex < |routes|
  requires forall i :: 0 <= i < |routes| ==> routes[i].1 > 0
{
  forall i :: 0 <= i < |routes| ==> 
    getNextArrivalTime(routes[routeIndex].0, routes[routeIndex].1, t) <= 
    getNextArrivalTime(routes[i].0, routes[i].1, t)
}

// <vc-helpers>
lemma lemma_getNextArrivalTimeMonotonic(firstTime: int, interval: int, targetTime1: int, targetTime2: int)
  requires interval > 0
  requires targetTime1 <= targetTime2
  ensures getNextArrivalTime(firstTime, interval, targetTime1) <= getNextArrivalTime(firstTime, interval, targetTime2)
{
  if firstTime >= targetTime2 {
    assert firstTime >= targetTime1;
    assert getNextArrivalTime(firstTime, interval, targetTime1) == firstTime;
    assert getNextArrivalTime(firstTime, interval, targetTime2) == firstTime;
  } else if firstTime >= targetTime1 {
    assert getNextArrivalTime(firstTime, interval, targetTime1) == firstTime;
    assert getNextArrivalTime(firstTime, interval, targetTime2) >= firstTime;
  } else {
    var diff1 := targetTime1 - firstTime;
    var diff2 := targetTime2 - firstTime;
    var q1 := (diff1 + interval - 1) / interval;
    var q2 := (diff2 + interval - 1) / interval;
    lemma_div_property(diff1, interval, diff2);
    assert q1 <= q2;
    assert getNextArrivalTime(firstTime, interval, targetTime1) == firstTime + q1 * interval;
    assert getNextArrivalTime(firstTime, interval, targetTime2) == firstTime + q2 * interval;
  }
}

lemma lemma_div_property(a: int, d: int, k: int)
  requires d > 0
  requires a <= k
  ensures (a + d - 1) / d <= (k + d - 1) / d
{
  if a <= k {
    var q1 := (a + d - 1) / d;
    var q2 := (k + d - 1) / d;
    if q1 > q2 {
      assert q1 * d > k;
      assert (q1 - 1) * d < a;
      assert false;
    }
  }
}

lemma lemma_getNextArrivalTimeProperty(firstTime: int, interval: int, targetTime: int)
  requires interval > 0
  ensures getNextArrivalTime(firstTime, interval, targetTime) >= firstTime
  ensures getNextArrivalTime(firstTime, interval, targetTime) >= targetTime || 
           getNextArrivalTime(firstTime, interval, targetTime) == firstTime
{
  if firstTime >= targetTime {
    assert getNextArrivalTime(firstTime, interval, targetTime) == firstTime;
  } else {
    var diff := targetTime - firstTime;
    var q := (diff + interval - 1) / interval;
    assert q >= 0;
    assert firstTime + q * interval >= firstTime;
    assert firstTime + q * interval >= targetTime;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, t: int, routes: seq<(int, int)>) returns (result: int)
  requires ValidInput(n, t, routes)
  ensures 1 <= result <= n
  ensures IsOptimalRoute(routes, t, result - 1)
// </vc-spec>
// <vc-code>
{
  var bestIndex := 0;
  var minTime := getNextArrivalTime(routes[0].0, routes[0].1, t);
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= bestIndex < i
    invariant minTime == getNextArrivalTime(routes[bestIndex].0, routes[bestIndex].1, t)
    invariant IsOptimalRoute(routes[0..i], t, bestIndex)
  {
    var currentTime := getNextArrivalTime(routes[i].0, routes[i].1, t);
    if currentTime < minTime {
      bestIndex := i;
      minTime := currentTime;
      assert IsOptimalRoute(routes[0..(i+1)], t, bestIndex);
    } else if currentTime == minTime && routes[i].0 < routes[bestIndex].0 {
      bestIndex := i;
      minTime := currentTime;
      assert IsOptimalRoute(routes[0..(i+1)], t, bestIndex);
    } else {
      assert IsOptimalRoute(routes[0..i], t, bestIndex);
      assert getNextArrivalTime(routes[bestIndex].0, routes[bestIndex].1, t) <= currentTime;
      assert IsOptimalRoute(routes[0..(i+1)], t, bestIndex);
    }
    i := i + 1;
  }
  
  result := bestIndex + 1;
}
// </vc-code>

