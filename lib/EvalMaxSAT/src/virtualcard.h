#ifndef VIRTUALCARD_H
#define VIRTUALCARD_H

#include <sstream>
#include <vector>
#include <cassert>

class VirtualSAT;

class VirtualCard {


protected:
    VirtualSAT *solver;
    unsigned int nbLit;
    unsigned int bound;

public:

    VirtualCard(VirtualSAT *solver, const std::vector<int> &clause, unsigned int bound=0)
        : solver(solver), nbLit(static_cast<unsigned int>(clause.size())), bound(bound) {

    }

   VirtualCard(VirtualSAT *solver, int nbLits, unsigned int bound=0)
           : solver(solver), nbLit(nbLits), bound(bound) {

   }

    virtual std::vector<int> getClause() = 0;

    virtual ~VirtualCard();

    virtual int operator <= (unsigned int k) {
        return atMost(k);
    }

    virtual unsigned int size() const {
        return nbLit;
    }

    virtual void print(std::ostream& os) const {
        os << "VirtualCard(size: "<<nbLit<<", bound: " << bound << ")";
    }

    virtual int atMost(unsigned int k) = 0;

};


#endif // VIRTUALCARD_H
