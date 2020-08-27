#include <map>

#ifndef NTS_UTIL_H
#define NTS_UTIL_H

template <class T, class U>
std::vector<T> map_fn(T(*f)(U), std::vector<U> vec) {
  // make a new vector by applying a function to all arguments of an existing one
  int size = vec.size();
  std::vector<T> ans;
  ans.reserve(size);
  for (int i = 0; i < size; i++)
    ans.push_back(f(vec[i]));
  return ans;
}

template <class T, class U> class stackmap {
private:
  // lower stack elements...
  stackmap<T, U> *prev;
  // own elements:
  std::map<T, U> curr;
public:
  stackmap<T, U>(stackmap<T, U> *prev_stmp) : prev(prev_stmp) {};
  
  // check if we contain a particular key:
  bool has(T key) {
    if (curr.find(key) == curr.end()) {
      if (prev == NULL)
        return false;
      return prev->has(key);
    }
    return true;
  }

  // access element using key
  U& at(T key) {
    if (prev == NULL)
      return curr.at(key);
    typename std::map<T, U>::iterator iter = curr.find(key);
    if (iter == curr.end())
      return prev->at(key);
    return iter->second;
  }

  // modify the map on top of the stack
  void set(T key, U val) {
    // only modifies top level of dictionary :)
    curr[key] = val;
  }

  // return the stackmap underneath this one
  stackmap<T, U> *pop() {
    return prev;
  }
};
 
#endif

