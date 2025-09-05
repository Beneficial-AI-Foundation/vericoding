Given the number pledged for a year, current value and name of the month, return string that gives information about the challenge status:

- ahead of schedule
- behind schedule
- on track
- challenge is completed

Examples:

`(12, 1, "February")` - should return `"You are on track."`

`(12, 1, "March")` - should return `"You are 1 behind schedule."`

`(12, 5, "March")` - should return `"You are 3 ahead of schedule."`

`(12, 12, "September")` - should return `"Challenge is completed."`

Details:
- you do not need to do any prechecks (input will always be a natural number and correct name of the month)
- months should be as even as possible (i.e. for 100 items: January, February, March and April - 9, other months 8)
- count only the item for completed months (i.e. for March check the values from January and February) and it means that for January you should always return `"You are on track."`.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
