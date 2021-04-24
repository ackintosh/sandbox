import React from 'react';
import ReactDOM from 'react-dom';

import './main';
import {ArwesThemeProvider, Button, FrameBox, StylesBaseline, Text} from "@arwes/core";
import {Animator, AnimatorGeneralProvider} from "@arwes/animation";
import {bootstrap} from "./main";

// import '../public/index.css';

const FONT_FAMILY_ROOT = '"Titillium Web", sans-serif';
const FONT_FAMILY_CODE = '"Source Code Pro", monospace';

const generalAnimator = { duration: { enter: 500, exit: 500 } };


const App = () => {
    const [activate, setActivate] = React.useState(true);

    // React.useEffect(() => {
    //     const timeout = setTimeout(() => setActivate(!activate), 2000);
    //     return () => clearTimeout(timeout);
    // }, [activate]);

    return (
        <ArwesThemeProvider>
            <StylesBaseline styles={{
                'html, body': { fontFamily: FONT_FAMILY_ROOT },
                'code, pre': { fontFamily: FONT_FAMILY_CODE },
                'body': { textAlign: "center" }
            }} />
            <AnimatorGeneralProvider animator={generalAnimator}>
                <Animator animator={{ activate, manager: 'stagger' }}>
                    <Text as='h1'>Tracing</Text>
                    <hr />
                    <FrameBox>
                        <div style={{width: 500, height: 200}}>
                        <div>
                            <Text as='p'>description</Text>
                        </div>
                        <div>
                            <Button
                                animator={{ activate }}
                                onClick={bootstrap}
                            >
                                <Text>Choose Trace File</Text>
                            </Button>
                        </div>
                        </div>
                    </FrameBox>
                </Animator>
            </AnimatorGeneralProvider>
        </ArwesThemeProvider>
    );
};

ReactDOM.render(
    <React.StrictMode>
        <App />
    </React.StrictMode>,
    document.getElementById('root')
);

