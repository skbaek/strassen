def spaces : nat → string 
| 0 := ""
| (n+1) := " " ++ spaces n

def string.pad (l s) : string := 
s ++ spaces (l - s.length)