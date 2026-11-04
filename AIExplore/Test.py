from math import *

nums = [1, 2, 4, 5, 4, 2, 3, 3, 3, 4, 5, 5, 5, 5, 5]

def count_frequency(numbers: list[int]):
  freq : dict = {}
  for n in numbers:
    freq[n] = 0
  for n in range(len(numbers)):
    freq[(numbers[n])] = freq[(numbers[n])] + 1
  return freq

def count_frequency1(nums):
    freq = {}
    for n in nums:
        if n in freq:
            freq[n] += 1
        else:
            freq[n] = 1
    return freq

print(count_frequency(nums))
print(count_frequency1(nums))

def is_prime(n):
  if n <= 1 or not isinstance(n, int):
    return False
  else:
    for m in range(2, isqrt(n)+1):
      if n % m == 0:
        return False
    return True

print(is_prime(101))
