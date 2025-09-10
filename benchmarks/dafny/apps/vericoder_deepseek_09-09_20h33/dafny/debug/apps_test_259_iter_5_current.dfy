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
    var diff2 := targetTime2 - firstTime;
    var q2 := (diff2 + interval - 1) / interval;
    assert q2 >= 0;
    assert getNextArrivalTime(firstTime, interval, targetTime2) == firstTime + q2 * interval;
    assert firstTime <= firstTime + q2 * interval;
  } else {
    var diff1 := targetTime1 - firstTime;
    var diff2 := targetTime2 - firstTime;
    var q1 := (diff1 + interval - 1) / interval;
    var q2 := (diff2 + interval - 1) / interval;
    assert diff1 <= diff2;
    
    // Prove q1 <= q2
    assert (diff1 + interval - 1) / interval <= (diff2 + interval - 1) / interval
      by {
        var d1 := diff1 + interval - 1;
        var d2 := diff2 + interval - 1;
        assert d1 <= d2;
        if d1 < 0 {
          assert q1 == 0 && q2 >= 0;
        } else {
          assert d1 >= 0 && d2 >= 0;
          assert q1 <= q2;
        }
      };
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
    var nextTime := firstTime + q * interval;
    assert nextTime >= firstTime;
    if q == 0 {
      assert nextTime == firstTime;
    } else {
      assert nextTime >= targetTime;
    }
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
  lemma_getNextArrivalTimeProperty(routes[0].0, routes[0].1, t);
  
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= bestIndex < i
    invariant minTime == getNextArrivalTime(routes[bestIndex].0, routes[bestIndex].1, t)
    invariant forall j :: 0 <= j < i ==> minTime <= getNextArrivalTime(routes[j].0, routes[j].1, t)
  {
    var currentTime := getNextArrivalTime(routes[i].0, routes[i].1, t);
    lemma_getNextArrivalTimeProperty(routes[i].0, routes[i].1, t);
    lemma_getNextArrivalTimeMonotonic(routes[i].0, routes[i].1, t, t);
    if currentTime < minTime {
      bestIndex := i;
      minTime := currentTime;
    } else if currentTime == minTime {
      if routes[i].0 < routes[bestIndex].0 {
        bestIndex := i;
        minTime := currentTime;
      }
    }
    i := i + 1;
  }
  
  result := bestIndex + 1;
}
// </vc-code>

