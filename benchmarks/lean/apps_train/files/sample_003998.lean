If the first day of the month is a Friday, it is likely that the month will have an `Extended Weekend`. That is, it could have five Fridays, five Saturdays and five Sundays. 

In this Kata, you will be given a start year and an end year. Your task will be to find months that have extended weekends and return:
```
- The first and last month in the range that has an extended weekend
- The number of months that have extended weekends in the range, inclusive of start year and end year.
```

For example:
```python
solve(2016,2020) = ("Jan","May",5). #The months are: Jan 2016, Jul 2016, Dec 2017, Mar 2019, May 2020
```

More examples in test cases. Good luck!

If you found this Kata easy, please try [myjinxin2015](https://www.codewars.com/users/myjinxin2015) challenge version [here](https://www.codewars.com/kata/extended-weekends-challenge-edition)

def monthAbbr : Month → String
| Month.Jan => "Jan"
| Month.Feb => "Feb" 
| Month.Mar => "Mar"
| Month.Apr => "Apr"
| Month.May => "May"
| Month.Jun => "Jun"
| Month.Jul => "Jul"
| Month.Aug => "Aug"
| Month.Sep => "Sep"
| Month.Oct => "Oct"
| Month.Nov => "Nov"
| Month.Dec => "Dec"

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded