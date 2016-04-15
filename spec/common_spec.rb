require 'spec_helper'

describe 'infrastructure::common' do
  let(:hostname) { 'the-hostname' }
  let(:project_root) { 'the-project-root' }

  let(:chef_run) do
    ChefSpec::SoloRunner.new do |node|
      node.automatic['hostname'] = hostname
      node.set['infrastructure']['project_root'] = project_root
    end.converge(described_recipe)
  end

  it 'includes apt' do
    expect(chef_run).to include_recipe('apt')
  end

  it 'adds the git apt repository' do
    code_name = chef_run.node['lsb']['codename']
    expect(chef_run).to add_apt_repository('git-ppa').with(
      uri: 'http://ppa.launchpad.net/git-core/ppa/ubuntu',
      distribution: code_name,
      components: %w(main),
      key: 'E1DF1F24',
      keyserver: 'keyserver.ubuntu.com')
  end

  %w(
    bash-completion
    curl
    dstat
    git
    iftop
    iotop
    iperf
    jq
    lsof
    man-db
    mlocate
    nano
    strace
    sysstat
    unzip
    wget
    zip
  ).each do |package|
    it "installs #{package}" do
      expect(chef_run).to install_package(package)
    end
  end

  it 'installs bundler dependencies if Gemfile exists' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Gemfile").and_return(true)
    expect(chef_run).to run_execute('bundle-install').with(
      command: "bundle install --gemfile=#{project_root}/Gemfile",
      user: 'vagrant')
  end

  it 'does not install bundler dependencies if Gemfile is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Gemfile").and_return(false)
    expect(chef_run).to_not run_execute('bundle-install')
  end
end
