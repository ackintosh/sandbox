#!/usr/bin/env ruby


def binary_search(a, b)
  for target in b do
    print "#{binary_search_inner(a, target, 0, a.length - 1)} "
  end
end

def binary_search_inner(input, target, l, r)
  return -1 if l > r

  m = (l + r) / 2
  if input[m] > target then
    return binary_search_inner(input, target, l, m - 1)
  elsif input[m] < target then
    return binary_search_inner(input, target, m + 1, r)
  else
    tmp = m
    result = m
    while input[tmp] == target do
        result = tmp
        tmp -= 1
    end
    return result
  end
end

if __FILE__ == $0
  n = gets.to_i
  a = gets.split().map(&:to_i)
  n = gets.to_i
  b = gets.split().map(&:to_i)

  binary_search(a, b)
end
