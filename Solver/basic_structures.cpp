/**
* @author Tim Luchterhand
* @date 26.11.24
* @brief
*/

#include "basic_structures.hpp"
#include "util/exception.hpp"

using namespace std;

namespace sat {


    Variable::Variable(unsigned val) :
        val(val) {}

    unsigned Variable::get() const {
        return this->val;
    }

    bool Variable::operator==(Variable other) const {
        return this->val == other.val;
    }

    Literal::Literal(unsigned val) :
        val(val) {}

    unsigned Literal::get() const {
        return this->val;
    }

    Literal Literal::negate() const {
        if (this->val % 2 == 0) {
            return Literal(this->val + 1);

        } else {
            return Literal(this->val - 1);
        }
    }

    short Literal::sign() const {
        if (this->val % 2 == 0) {
            return -1;

        } else {
            return 1;
        }
    }

    bool Literal::operator==(Literal other) const {
        return this->val == other.val;
    }

    bool Literal::operator<(Literal other) const {
        return this->val < other.val;
    }

    bool Literal::operator>(Literal other) const {
        return this->val > other.val;
    }

    Literal pos(Variable x) {
        return Literal(2 * x.get() + 1);
    }

    Literal neg(Variable x) {
        return Literal(2 * x.get());
    }

    Variable var(Literal l) {
        return Variable(l.get()/2);
    }
}
