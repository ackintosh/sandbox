// https://leetcode.com/problems/design-browser-history/

#[derive(Debug)]
struct BrowserHistory {
    history: Vec<String>,
    current: usize,
}

/**
 * `&self` means the method takes an immutable reference
 * If you need a mutable reference, change it to `&mut self` instead
 */
impl BrowserHistory {
    fn new(homepage: String) -> Self {
        BrowserHistory {
            history: vec![homepage],
            current: 0,
        }
    }

    fn visit(&mut self, url: String) {
        let i = self.current + 1;
        while self.history.get(i).is_some() {
            self.history.remove(i);
        }

        self.history.push(url);
        self.current += 1;
    }

    fn back(&mut self, steps: i32) -> String {
        self.current = self.current.saturating_sub(steps as usize);
        self.history
            .get(self.current)
            .expect("should have history")
            .clone()
    }

    fn forward(&mut self, steps: i32) -> String {
        self.current = self
            .current
            .saturating_add(steps as usize)
            .min(self.history.len() - 1);
        self.history
            .get(self.current)
            .expect("should have history")
            .clone()
    }
}

/**
 * Your BrowserHistory object will be instantiated and called as such:
 * let obj = BrowserHistory::new(homepage);
 * obj.visit(url);
 * let ret_2: String = obj.back(steps);
 * let ret_3: String = obj.forward(steps);
 */

#[test]
fn test() {
    let mut browser_history = BrowserHistory::new("leetcode.com".into());
    // println!("{:?}", browser_history);
    browser_history.visit("google.com".into());
    // println!("{:?}", browser_history);
    browser_history.visit("facebook.com".into());
    // println!("{:?}", browser_history);
    browser_history.visit("youtube.com".into());
    // println!("{:?}", browser_history);

    assert_eq!("facebook.com".to_string(), browser_history.back(1));
    // println!("{:?}", browser_history);
    assert_eq!("google.com".to_string(), browser_history.back(1));
    // println!("{:?}", browser_history);

    assert_eq!("facebook.com".to_string(), browser_history.forward(1));
    browser_history.visit("linkedin.com".into());
    // println!("{:?}", browser_history);
    assert_eq!("linkedin.com".to_string(), browser_history.forward(2));
    // println!("{:?}", browser_history);

    assert_eq!("google.com".to_string(), browser_history.back(2));
    // println!("{:?}", browser_history);
    assert_eq!("leetcode.com".to_string(), browser_history.back(7));
    // println!("{:?}", browser_history);
}

#[test]
fn test2() {
    let mut browser_history = BrowserHistory::new("jrbilt.com".into());
    browser_history.visit("uiza.com".into());
    browser_history.forward(3);
    browser_history.forward(3);
    browser_history.visit("fveyl.com".into());
    browser_history.visit("hyhqfqf.com".into());
    // println!("{:?}", browser_history);
    browser_history.back(3);
    // println!("{:?}", browser_history);
    browser_history.visit("cccs.com".into());
    // println!("{:?}", browser_history);
    browser_history.visit("bivz.com".into());
    // println!("{:?}", browser_history);
    assert_eq!("bivz.com".to_string(), browser_history.forward(6));
    // println!("{:?}", browser_history);
    assert_eq!("cccs.com".to_string(), browser_history.back(1));
    // println!("{:?}", browser_history);
}
