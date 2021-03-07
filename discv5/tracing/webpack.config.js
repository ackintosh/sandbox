const path = require('path');
const webpack = require('webpack');

module.exports = {
  entry: './src/main.js',
  output: {
    filename: 'bundle.js',
    path: path.join(__dirname, 'public')
  },
  devServer: {
    contentBase: "public",
    open: true
  },
  plugins: [
    // THREE.Scene などの形式で three.js のオブジェクトを使用できるようにする
    new webpack.ProvidePlugin({
      THREE : 'three/build/three'
    }),
  ]
};
