#ifndef CADICALINTERFACE_H
#define CADICALINTERFACE_H

#include "virtualsat.h"

#include "../../cadical/src/cadical.hpp"

#include "coutUtil.h"
#include "Chrono.h"

#include <thread>
#include <future>
#include <iostream>
#include <chrono>



class CadicalInterface : public VirtualSAT {
    CaDiCaL::Solver *solver;
    unsigned int nVar = 0;
    //int conflictSize;
    CadicalInterface( CaDiCaL::Solver* solver, unsigned int nVar=0 )
        : solver(solver), nVar(nVar){
    }

public:

    CadicalInterface()
        : solver(new CaDiCaL::Solver()) {

        solver->set("stabilize", 0);
    }
    
    VirtualSAT* clone() override {
        CaDiCaL::Solver *copySolver = new CaDiCaL::Solver;
        solver->copy(*copySolver);
        
        return new CadicalInterface(copySolver, nVar);
    }

    ~CadicalInterface() override;

   // For a given unit clause to have the passed value, give the required value for every other concerned literal
   // or return false if there is no solution
    bool propagate(const std::vector<int> &assum, std::vector<int> &result) override {
        return solver->find_up_implicants(assum, result);
    }

   virtual int newVar(bool decisionVar=true) override {
        // decisionVar not implemented in Cadical ?
        return ++nVar;
    }

    virtual unsigned int nVars() override {
        return nVar;
    }

   virtual void addClause( const std::vector<int> &clause ) override {
        for (int lit : clause) {
            solver->add(lit);
        }
       solver->add(0);
   }

   bool solve() override {
        bool result = solver->solve();
        return result;
    }

    std::vector<int> getConflict(const std::vector<int> &assumptions) override {
        std::vector<int> conflicts;
        for (int lit : assumptions) {
            if (solver->failed(lit)) {
                conflicts.push_back(lit);
            }
        }
        return conflicts;
    }

   std::vector<int> getConflict(const std::set<SetLit> &assumptions) override {
       std::vector<int> conflicts;
       for (SetLit setLit : assumptions) {
           if (solver->failed(setLit.lit)) {
               conflicts.push_back(setLit.lit);
           }
       }
       return conflicts;
   }


   unsigned int conflictSize() override {
	    return solver->conflictSize();
    }

    int solveLimited(const std::vector<int> &assumption, int confBudget, int except=0) override {

        solver->reset_assumptions();

        for (int lit : assumption) {
            if (lit == except)
                continue;
            solver->assume(lit);
        }

        solver->limit("conflicts", confBudget);

        auto result = solver->solve();

        // TODO: Fix these hardcoded values for enums...
        if(result==10) { // Satisfiable
            return 1;
        }
        if(result==20) { // Unsatisfiable
            return 0;
        }
        if(result==0) { // Limit
            return -1;
        }

        assert(false);
        return 0;
    }

    int solveLimited(const std::list<int> &assumption, int confBudget, int except=0) override {
        solver->reset_assumptions();

        for (int lit : assumption) {
            if (lit == except)
                continue;
            solver->assume(lit);
        }

        solver->limit("conflicts", confBudget);

        auto result = solver->solve();

        if(result==10) { // Satisfiable
            return 1;
        }
        if(result==20) { // Unsatisfiable
            return 0;
        }
        if(result==0) { // Limit
            return -1;
        }

        assert(false);
        return 0;
    }

   int solveLimited(const std::set<SetLit> &assumption, int confBudget, int except) override {
       solver->reset_assumptions();

       for (SetLit SetLit : assumption) {
           if (SetLit == except)
               continue;
           solver->assume(SetLit.lit);
       }

       solver->limit("conflicts", confBudget);

       auto result = solver->solve();

       if(result==10) { // Satisfiable
           return 1;
       }
       if(result==20) { // Unsatisfiable
           return 0;
       }
       if(result==0) { // Limit
           return -1;
       }

       assert(false);
       return 0;
   }

    int solveLimited(const std::set<int> &assumption, int confBudget, int except) override {
        solver->reset_assumptions();

        for (int lit : assumption) {
            if (lit == except)
                continue;
            solver->assume(lit);
        }

        solver->limit("conflicts", confBudget);

        auto result = solver->solve();

        if(result==10) { // Satisfiable
            return 1;
        }
        if(result==20) { // Unsatisfiable
            return 0;
        }
        if(result==0) { // Limit
            return -1;
        }

        assert(false);
        return 0;
    }

    bool solve(const std::vector<int> &assumption) override {
        for (int lit : assumption) {
            solver->assume(lit);
        }

        int result = solver->solve();

        assert( (result == 10) || (result == 20) );

        return result == 10; // Sat
    }


   bool solve(const std::set<SetLit> &assumption) override {
       for (SetLit setLit : assumption) {
           solver->assume(setLit.lit);
       }

       int result = solver->solve();

       assert( (result == 10) || (result == 20) );

       return result == 10; // Sat
   }


    bool getValue(unsigned int var) override {
        return (solver->val(var) > 0);
    }

};
CadicalInterface::~CadicalInterface() {
    delete solver;
}


#endif
