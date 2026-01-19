/**
* @author Tim Luchterhand
* @date 27.11.24
* @brief
*/

#include "Solver.hpp"
#include "util/exception.hpp"

namespace sat {
    Solver::Solver(unsigned numVariables) :
        numVariables(numVariables) {
            this->clauses = std::vector<ClausePointer>();
            this->model = std::unordered_map<unsigned, TruthValue>();
            this->unitLiterals = std::vector<Literal>();

            this->model.reserve(numVariables);

            for (unsigned i = 0; i < numVariables; i++) {
                this->model[i] = TruthValue::Undefined;
            }

            this->watches.reserve(2*numVariables);

            for (unsigned i = 0; i < 2*numVariables; i++) {
                this->watches[i] = std::vector<ClausePointer>();
            }
        }

    bool Solver::addClause(Clause clause) {
        if (clause.isEmpty()) {
            return false;
        }

        if (clause.size() == 1) {
            Literal l = clause[0];

            if (falsified(l)) {
                return false;
            }

            this->unitLiterals.push_back(l);
            return true;
        }

        this->clauses.push_back(std::make_shared<Clause>(clause));


        // Update watches
        Literal firstWatcher = clause.getWatcherByRank(0);
        Literal secondWatcher = clause.getWatcherByRank(1);

        if (firstWatcher != -1) {
            this->watches[firstWatcher.get()].push_back(this->clauses.back());
        }

        if (secondWatcher != -1) {
            this->watches[secondWatcher.get()].push_back(this->clauses.back());
        }

        return true;
    }

    /**
     * Here you have a possible implementation of the rebase-method. It should work out of the box.
     * To use it, remove the throw-expression and un-comment the code below. The implementation requires that
     * your solver has some sort of container of pointer types to clause called 'clauses'
     * (e.g. std::vector<ClausePointer>). Additionally, your solver needs to have a container of unit literals
     * called 'unitLiterals'.
     */
    auto Solver::rebase() const -> std::vector<Clause> {    
        std::vector<Clause> reducedClauses;
        // We check all clauses in the solver. If the clause is SAT (at least one literal is satisfied), we don't include it.
        // Additionally, we remove all falsified literals from the clauses since we only care about unassigned literals.
        for (const auto &c: clauses) {
            bool sat = false;
            // We're creating a new (possibly smaller clause from the current clause c)
            std::vector<Literal> newLits;
            newLits.reserve(c->size());
            // For each literal l in the clause we check if l is satisfied or falsified
            for (auto l: *c) {
                if (satisfied(l)) {
                    // in this case, the whole clause is satisfied and can be removed entirely from the solver
                    sat = true;
                    break;
                }

                if (!falsified(l)) {
                    // only unassigned literals are added to the reduced clause
                    newLits.emplace_back(l);
                }
            }

            if (!sat) {
                // create the new clause (move all the literals inside the Clause-class)
                Clause newClause(std::move(newLits));
                // Check if we already added an equivalent clause
                auto res = std::ranges::find_if(reducedClauses, [&newClause](const auto &clause) {
                    return clause.sameLiterals(newClause);
                });
                if (res == reducedClauses.end()) {
                    // The new clause is not yet contained => add it
                    reducedClauses.emplace_back(std::move(newClause));
                }
            }
        }

        // Finally, we need to add all the unit literals as well
        for (Literal l: unitLiterals) {
            reducedClauses.emplace_back(std::vector{l});
        }

        return reducedClauses;
    }

    TruthValue Solver::val(Variable x) const {       
        return this->model.at(x.get());
    }

    bool Solver::satisfied(Literal l) const {
        TruthValue value = val(var(l));

        if ((value == TruthValue::False) && (l.sign() == -1)) {
            return true;

        } else if ((value == TruthValue::True) && (l.sign() == 1)) {
            return true;

        } else {
            return false;
        }
    }

    bool Solver::falsified(Literal l) const {
        TruthValue value = val(var(l));
        
        if ((value == TruthValue::False) && (l.sign() == 1)) {
            return true;

        } else if ((value == TruthValue::True) && (l.sign() == -1)) {
            return true;

        } else {
            return false;
        }
    }

    bool Solver::assign(Literal l) {
        if (falsified(l)) {
            return false;
        }

        if(satisfied(l)) {
            return true;
        }
        
        this->unitLiterals.push_back(l);

        if (l.sign() == 1) {
            this->model[var(l).get()] = TruthValue::True;
            
        } else {
            this->model[var(l).get()] = TruthValue::False;
        }
        return true;
    }

    bool Solver::unitPropagate() {
        unsigned toPropagate = 0;
        while (toPropagate < this->unitLiterals.size()) {
            Literal current = this->unitLiterals[toPropagate].negate();

            bool res = true;

            for (const auto &clausePtr : this->watches[current.get()]) {
                size_t r = clausePtr->getRank(current);
                size_t i = clausePtr->getIndex(r);
                size_t start = i;
                Literal p = clausePtr->getWatcherByRank(1 - r);

                if (!satisfied(p)) {
                    while(true) {
                        i += 1;
                        if (i == clausePtr->size()) {
                            i = 0;
                        }
                        if (i == start) {
                            break;
                        }
                        if ((*clausePtr)[i] != p) {
                            if (!falsified((*clausePtr)[i])) {
                                auto it = std::ranges::find(this->watches[current.get()], clausePtr);
                                this->watches[current.get()].erase(it);

                                clausePtr->setWatcher((*clausePtr)[i], r);
                                this->watches[(*clausePtr)[i].get()].push_back(clausePtr);
                                break;
                            }
                        }
                    }
                    if (i == start) {
                        if (falsified(p)) {
                            res = false;

                        } else {
                            this->unitLiterals.push_back(p);
                            assign(p);
                        }
                    }
                }

                
            }

            if (!res) {
                return false;
            }

            toPropagate++;

        }
        return true;
    }
} // sat