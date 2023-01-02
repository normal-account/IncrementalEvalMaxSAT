#ifndef NEWEVALMAXSAT_CARD_REUSAL_H
#define NEWEVALMAXSAT_CARD_REUSAL_H
#include <map>
#include <set>
#include <optional>
#include <vector>


class Node {
public:
   bool visited = false;
   std::map<int, Node> children;
   std::optional<std::list<std::vector<int>>> core;
};


#endif //NEWEVALMAXSAT_CARD_REUSAL_H
