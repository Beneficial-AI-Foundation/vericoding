In this task you have to code process planner.

You will be given initial thing, target thing and a set of processes to turn one thing into another (in the form of _[process\_name, start\_thing, end\_thing]_). You must return  names of shortest sequence of processes to turn initial thing into target thing, or empty sequence if it's impossible.

If start already equals end, return [], since no path is required.

Example: 

```python
test_processes = [
        ['gather', 'field', 'wheat'],
        ['bake', 'flour', 'bread'],
        ['mill', 'wheat', 'flour']
];

processes('field', 'bread', test_processes) # should return ['gather', 'mill', 'bake']
processes('field', 'ferrari', test_processes) # should return []
processes('field', 'field', test_processes) # should return [], since no processes are needed
```

Good luck!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
