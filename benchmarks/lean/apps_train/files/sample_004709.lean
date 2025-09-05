The description is rather long but you are given all needed formulas (almost:-)

John has bought a bike but before going moutain biking he wants us to do a few simulations.

He gathered information:

- His trip will consist of an ascent of `dTot` kilometers with an average slope of `slope` *percent* 
- We suppose that: there is no wind, John's mass is constant `MASS = 80 (kg)`, his power (generated at time `t` by pedaling and measured in watts)
at the start of the trip is `WATTS0 = 225 (watts)`
- We don't take account of the rolling resistance
- When he starts climbing at t = 0 his initial speed (pushed start) is `v0 (km/h)`
- His initial acceleration `gamma` is 0.
`gamma` is in `km/h/min` at time `t`. It is the number of kilometers per hour he gains or loses in the next *minute*. 
- Our time step is `DELTA_T = 1.0 / 60.0` (in minutes)

Furthermore (constants in uppercase are given below):

 - Because of tiredness, he *loses* D_WATTS * DELTA_T of power at each DELTA_T. 
 - calcul of acceleration:

  Acceleration has three components:
    - 1) on an ascent where the slope is `slope` the effect of earth gravity is given by:

    `- GRAVITY_ACC * function(slope)`

    (Beware: here the `slope`is a percentage, it is not an angle. You have to determine `function(slope)`).

    Some help for `function(slope)`:

    a) slope: 

    b) earth gravity:

    https://en.wikipedia.org/wiki/Gravity_of_Earth

    - 2) air drag is 

    `- DRAG * abs(v) * abs(v) / MASS` where `v` is his current speed

    - 3) if his power and his speed are both strictly positive we add the thrust (by pedaling) which is: 

    `+ G_THRUST * watts / (v * MASS)` where `watts` is his current power

    - 4) if his total `acceleration is <= 1e-5` we set acceleration to 0
 - If `v - 3.0 <= 1e-2` John gives up

```
Constants:
GRAVITY_ACC = 9.81 * 3.6 * 60.0                        // gravity acceleration
DRAG        = 60.0 * 0.3 / 3.6                         // force applied by air on the cyclist
DELTA_T     = 1.0 / 60.0                               // in minutes
G_THRUST    = 60 * 3.6 * 3.6                           // pedaling thrust
MASS        = 80.0                                     // biker's mass
WATTS0      = 225.0                                    // initial biker's power
D_WATTS     = 0.5                                      // loss of power
(Note: watts at time t + DELTA_T is watts at time t minus D_WATTS * DELTA_T)

Parameters:
double dTot                                            // distance to travel in km
double v0                                              // initial speed km/h
double slope                                           // ascent in percentage (don't forget to divide by 100 when needed)

Variables that can be used:
t                                                      // time
gamma                                                  // total acceleration with its 3 components
v                                                      // speed
d                                                      // distance travelled
watts                                                  // biker's power 

```
#### Task:
Write function
`temps(v0, slope, dTot)` which returns as a *rounded* integer the time `t` in minutes needed to travel `dTot`. 
If John gives up return `-1`.

As a reminder:

1) speed at (t + DELTA_T) = (speed at t) + gamma * DELTA_T

2) distance at (t + DELTA_T) can be taken as (distance at t) + speed * DELTA_T / 60.0 where speed is calculated with 1).

```
Examples:
temps(30, 5, 30) -> 114
temps(30, 20, 30) -> -1
temps(30, 8, 20) -> 110
```
Reference:

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded