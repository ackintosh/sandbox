window.addEventListener("DOMContentLoaded", init);

// ref https://ics.media/entry/14771/
function init() {
  const width = 960;
  const height = 540;

  // ///////////////////////////////////////
  // 1. レンダラーを作る
  // ///////////////////////////////////////
  const renderer = new THREE.WebGLRenderer({
    canvas: document.querySelector("#myCanvas")
  });

  // デフォルトではレンダラーのサイズが小さいため、setSize()メソッドでサイズを設定
  renderer.setSize(width, height);

  // スマホでも綺麗に見えるように、デバイスピクセル比も設定
  // これを設定しないとスマホだとぼやけてしまう
  renderer.setPixelRatio(window.devicePixelRatio);


  // ///////////////////////////////////////
  // 2. シーンを作る
  //
  // シーン: オブジェクトや光源などの置き場
  // ///////////////////////////////////////
  const scene = new THREE.Scene();


  // ///////////////////////////////////////
  // 3. カメラを作る
  //
  // Three.jsではカメラを作成し、その視点から見えるものがレンダラーを介してcanvasへ描画される
  // https://ics.media/entry/14771/images/concept.png
  // ///////////////////////////////////////
  // new THREE.PerspectiveCamera(画角, アスペクト比, 描画開始距離, 描画終了距離)
  const camera = new THREE.PerspectiveCamera(
    45,
    800 / 600,
    1,
    10000
  );
  camera.position.set(0, 0, +1000);


  // ///////////////////////////////////////
  // 4. 立方体を作る
  //
  // 立方体はメッシュという表示オブジェクトを使用して作成する
  // メッシュを作るには、ジオメトリ（形状）とマテリアル（素材）を用意する必要がある
  // ///////////////////////////////////////

  // *ジオメトリ（形状）を作る*
  // ジオメトリは頂点情報や面情報を持っている
  // 立方体や直方体のような箱状の形状を生成するための `BoxGeometry` を使用する
  // new THREE.BoxGeometry(幅, 高さ, 奥行き)
  // const geometry = new THREE.BoxGeometry(500, 500, 500);

  // *マテリアル（素材）を作る*
  // マテリアルは色や質感の情報を持っている
  // const material = new THREE.MeshStandardMaterial({
  //     color: 0x0000ff
  // });


  const geometry = new THREE.CircleGeometry( 200, 6);
  const material = new THREE.MeshBasicMaterial( { color: 0x1aff1a, transparent: true, opacity: 0.3, side: THREE.FrontSide } );
  // const material = new MeshPhongMaterial( { color: 0x156289, emissive: 0x072534, side: DoubleSide, flatShading: true } );


  // ジオメトリとマテリアルを使って、メッシュを作り、シーンに追加する
  // new THREE.Mesh(ジオメトリ,マテリアル)
  const box = new THREE.Mesh(geometry, material);
  // シーンに追加
  scene.add(box);


  // ///////////////////////////////////////
  // 5. ライトを作る
  // ///////////////////////////////////////
  // このままでは真っ暗なのでライトを作成する
  // DirectionalLight: 平行光源を意味します。平行光源は太陽光のように一定方向から差し込む光。
  // new THREE.DirectionalLight(色)
  const light = new THREE.DirectionalLight(0xffffff);
  light.intensity = 2; // 光の強さを倍に
  //  光源が斜めから差し込むようにライトの位置を変更しておく
  light.position.set(1, 1, 1);
  // ライトもシーンに追加することで反映される
  scene.add(light);


  // ///////////////////////////////////////
  // 6. 描画する
  // ///////////////////////////////////////
  // 下記だと、一度描画するだけなのでアニメーションできない
  // アニメーションさせるには、7. を行う
  // renderer.render(scene, camera);


  // ///////////////////////////////////////
  // 7. アニメーション
  // ///////////////////////////////////////
  tick();

  function tick() {
    requestAnimationFrame(tick);

    // 箱を回転させる
    // box.rotation.x += 0.01;
    // box.rotation.y += 0.01;

    // レンダリング
    renderer.render(scene, camera);
  }
}

