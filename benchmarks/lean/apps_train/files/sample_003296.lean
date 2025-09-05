# Task
 You have set an alarm for some of the week days.

 Days of the week are encoded in binary representation like this:
```
0000001 - Sunday
0000010 - Monday
0000100 - Tuesday
0001000 - Wednesday
0010000 - Thursday
0100000 - Friday 
1000000 - Saturday```
For example, if your alarm is set only for Sunday and Friday, the representation will be `0100001`. 

 Given the current day of the week, your task is to find the day of the week when alarm will ring next time.

# Example

 For `currentDay = 4, availableWeekDays = 42`, the result should be `6`.

 ```
currentDay = 4 means the current Day is Wednesday
availableWeekDays = 42 convert to binary is "0101010"
So the next day is 6 (Friday)
```

# Input/Output

 - `[input]` integer `currentDay`

 The weekdays range from 1 to 7, 1 is Sunday and 7 is Saturday

 - `[input]` integer `availableWeekDays`

 An integer. Days of the week are encoded in its binary representation.

 - `[output]` an integer

 The next day available.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible