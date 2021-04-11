export class LogKeyHelper {
    static increment(s) {
        const n = s.length / 2;
        const left = s.slice(0, n);
        const right = s.slice(n);
        const rightLength = right.length;

        const newRight = parseInt(right) + 1;

        if (newRight.toString().length > rightLength) {
            const newLeft = parseInt(left) + 1;
            return `${newLeft}${newRight.toString().slice(rightLength * -1)}`;
        } else {
            const zeros = (new Array(rightLength)).fill(0).join("");
            const zeroPrefixedRight = (zeros + newRight.toString()).slice(rightLength * -1);
            return `${left}${zeroPrefixedRight}`;
        }
    }

    static increase(s, n) {
        let result = s;
        for (let i = 0; i < n; i++) {
            result = LogKeyHelper.increment(result)
        }

        return result;
    }

    private static decrement(s) {
        const n = s.length / 2;
        const left = s.slice(0, n);
        const right = s.slice(n);
        const rightLength = right.length;

        const newRight = parseInt(right) - 1;

        if (newRight.toString().length === rightLength) {
            return `${left}${newRight}`;
        } else if (newRight === -1) {
            const newLeft = parseInt(left) - 1;
            const nineRight = (new Array(rightLength)).fill(9).join("");
            return `${newLeft}${nineRight}`;
        } else if (newRight.toString().length < rightLength) {
            const zeros = (new Array(rightLength)).fill(0).join("");
            const zeroPrefixedRight = (zeros + newRight.toString()).slice(rightLength * -1);
            return `${left}${zeroPrefixedRight}`;
        }
    }

    static decrease(s, n) {
        let result = s;
        for (let i = 0; i < n; i++) {
            result = LogKeyHelper.decrement(result)
        }

        return result;
    }

    static subtract(a, b) {
        let result = 0;
        while (a > b) {
            result++;
            a = LogKeyHelper.decrement(a);
        }
        return result;
    }
}
