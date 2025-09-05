Scientists working internationally use metric units almost exclusively. Unless that is, they wish to crash multimillion dollars worth of equipment on Mars.

Your task is to write a simple function that takes a number of meters, and outputs it using metric prefixes.

In practice, meters are only measured in "mm" (thousandths of a meter), "cm" (hundredths of a meter), "m" (meters) and "km" (kilometers, or clicks for the US military).

For this exercise we just want units bigger than a meter, from meters up to yottameters, excluding decameters and hectometers.

All values passed in will be positive integers.
e.g.

```python
meters(5);
// returns "5m"

meters(51500);
// returns "51.5km"

meters(5000000);
// returns "5Mm"
```

See http://en.wikipedia.org/wiki/SI_prefix for a full list of prefixes

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded