/**
* @author Tim Luchterhand
* @date 26.11.24
* @brief
*/

#include <cassert>
#include <algorithm>

#include "Clause.hpp"
#include "util/exception.hpp"

namespace sat {
    //TODO implementation here

    Clause::Clause(std::vector<Literal> literals) :
        literals(literals) {
            firstWatcher = literals.size() > 0 ? 0 : -1;
            secondWatcher = literals.size() > 1 ? 1 : -1;
        }

    short Clause::getRank(Literal l) const {
        if (l == literals.at(this->firstWatcher)) {
            return 0;

        } else if (l == literals.at(this->secondWatcher)) {
            return 1;

        } else {
            return -1;
        }
    }

    std::size_t Clause::getIndex(short rank) const {
        if (rank == 0) {
            return this->firstWatcher;

        } else {
            return this->secondWatcher;
        }
    }

    bool Clause::setWatcher(Literal l, short watcherNo) {
        auto it = std::find(literals.begin(), literals.end(), l);
        if (it != literals.end()) {
            if (watcherNo == 0) {
                this->firstWatcher = it - literals.begin();

            } else {
                this->secondWatcher = it - literals.begin();
            }
            return true;
        }
        return false;
    }

    auto Clause::begin() const -> std::vector<Literal>::const_iterator {
        return literals.begin();
    }

    auto Clause::end() const -> std::vector<Literal>::const_iterator {
        return literals.end();
    }

    bool Clause::isEmpty() const {
        return literals.empty();
    }

    Literal Clause::operator[](std::size_t index) const {
        return literals.at(index);
    }

    std::size_t Clause::size() const {
        return literals.size();
    }

    Literal Clause::getWatcherByRank(short rank) const {
        if (rank == 0) {
            return literals.at(this->firstWatcher);

        } else {
            return literals.at(this->secondWatcher);
        }
    }

    bool Clause::sameLiterals(const Clause &other) const {
        auto literalsCopy = this->literals;
        auto otherLiteralsCopy = other.literals;

        std::sort(literalsCopy.begin(), literalsCopy.end());
        std::sort(otherLiteralsCopy.begin(), otherLiteralsCopy.end());

        return literalsCopy == otherLiteralsCopy;
    }

}
