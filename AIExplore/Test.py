from math import *

nums = [1, 2, 4, 5, 4, 2, 3, 3, 3, 4, 5, 5, 5, 5, 5]

def count_frequency(numbers: list[int]):
  freq : dict = {}
  for n in numbers:
    freq[n] = 0
  for n in range(len(numbers)):
    freq[numbers[n]] = freq[numbers[n]] + 1
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

numbers = [3, 1, 5, 5, 5, 6]

def remove_duplicates(numbers):
  if numbers == []:
    return []
  else:
    record = []
    for n in numbers:
      if n not in record:
        record.append(n)
    return record

print(remove_duplicates(numbers))

proof_results = [
  {"theorem": "thm1", "status": "success", "error": None},
  {"theorem": "thm2", "status": "failed", "error": "unknown identifier"},
  {"theorem": "thm3", "status": "failed", "error": "type mismatch"},
  {"theorem": "thm4", "status": "success", "error": None},
  {"theorem": "thm5", "status": "failed", "error": "unknown identifier"},
  {"theorem": "thm6", "status": "failed", "error": "unsolved goals"} ]

print(proof_results[0]["error"] != None)

def analyse_errors(proof_results):
  data = {}
  for x in proof_results:
    if x["error"] != None:
      if x["error"] not in data:
        data[x["error"]] = [x["theorem"]]
      else:
        data[x["error"]].append(x["theorem"])
  return data

print(analyse_errors(proof_results))
