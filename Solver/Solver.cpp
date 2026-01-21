/**
* @author Tim Luchterhand
* @date 27.11.24
* @brief
*/

#include "Solver.hpp"
#include "util/exception.hpp"
#include "printing.hpp"

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

            assign(l);
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

        if ((value == TruthValue::False) && (l.sign() == -1)) return true;

        if ((value == TruthValue::True) && (l.sign() == 1)) return true;

        return false;
        
    }

    bool Solver::falsified(Literal l) const {
        TruthValue value = val(var(l));
        
        if ((value == TruthValue::False) && (l.sign() == 1)) return true;

        if ((value == TruthValue::True) && (l.sign() == -1)) return true;

        return false;
    }

    bool Solver::assign(Literal l) {
        if (falsified(l)) return false;

        if (satisfied(l)) return true;
        
        this->unitLiterals.push_back(l);

        if (l.sign() == 1) {
            this->model[var(l).get()] = TruthValue::True;
            
        } else this->model[var(l).get()] = TruthValue::False;
        
        return true;
    }

    bool Solver::unitPropagate() {
        size_t toPropagate = 0;

        while (toPropagate < unitLiterals.size()) {
            // std::cout << "To propagate index: " << toPropagate << std::endl;

            // std::cout << "Clauses" << std::endl;
            // printClauses();

            // std::cout << "Watches" << std::endl;
            // printWatches();
            
            // std::cout << "Unit literals : " << unitLiterals << std::endl;
            Literal l = unitLiterals[toPropagate];
            if (!assign(l)) return false;

            Literal current = l.negate();

            auto& watching = watches[current.get()];
            for (size_t k = 0; k < watching.size(); k++) {

                ClausePointer clausePtr = watching[k];
                size_t r = clausePtr->getRank(current);
                size_t i = clausePtr->getIndex(r);
                size_t start = i;
                Literal p = clausePtr->getWatcherByRank(1 - r);

                bool moved = false;

                if (!satisfied(p)) {
                    while (true) {
                        i++;
                        if (i == clausePtr->size()) i = 0;

                        if (i == start) break;

                        if ((*clausePtr)[i] != p && !falsified((*clausePtr)[i])) {
                            // Suppression en temps constant de la clause regardant l'ancien watcher
                            watching[k] = watching.back();
                            watching.pop_back();

                            // Ajout de la clause regardant le nouveau watcher
                            clausePtr->setWatcher((*clausePtr)[i], r);
                            
                            bool found = false;
                            for (auto& watch : watches[(*clausePtr)[i].get()]) {
                                if (watch->sameLiterals(*clausePtr)) {
                                    found = true;
                                    break;
                                }
                            }
                            if (!found) watches[(*clausePtr)[i].get()].push_back(clausePtr);
                            
                            moved = true;
                            k--;  // Nouvelle clause à la place de celle qu'on vient d'enlever, donc on incrémente pas k
                            break;
                        }
                    }

                    if (!moved && i == start) {
                        if (falsified(p)) return false;

                        assign(p);
                    }
                }                
            }

            ++toPropagate;
        }

    return true;
    }

    void Solver::printClauses() const {
        for (const auto &clause : clauses) {
            std::cout << *clause << std::endl;
        }
    }

    void Solver::printWatches() const {
        for (const auto& [lit, clauses] : watches) {
            std::cout << "Literal " << lit << " is watched by clauses:" << std::endl;
            for (const auto& clausePtr : clauses) {
                std::cout << *clausePtr << std::endl;
            }
        }
    }

} // sat